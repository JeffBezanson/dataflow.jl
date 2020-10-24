# Part 1: programs

import Base: convert

abstract type Exp end

struct Sym <: Exp
    name::Symbol
end

struct Num <: Exp
    val::Int
end

struct Call <: Exp
    head::Sym
    args::Vector{Exp}
end

abstract type Stmt end

struct Assign <: Stmt
    lhs::Sym
    rhs::Exp
end

struct Goto <: Stmt
    label::Int
end

struct GotoIf <: Stmt
    label::Int
    cond::Exp
end

struct Ret <: Stmt end

convert(::Type{Exp}, s::Symbol) = Sym(s)
convert(::Type{Sym}, s::Symbol) = Sym(s)
convert(::Type{Exp}, n::Int)    = Num(n)
convert(::Type{Num}, n::Int)    = Num(n)


# Part 2: lattices

# partial order, meet, join, top, bottom, and their identities

import Base: <=, ==, <, show

abstract type LatticeElement end

# Note: == and < are defined such that future LatticeElements only
# need to implement <=

<=(x::LatticeElement, y::LatticeElement) = x===y

==(x::LatticeElement, y::LatticeElement) = x<=y && y<=x

<(x::LatticeElement, y::LatticeElement) = x<=y && !(y<=x)

struct TopElement <: LatticeElement end
struct BotElement <: LatticeElement end

const ⊤ = TopElement()
const ⊥ = BotElement()

show(io::IO, ::TopElement) = print(io, "⊤")
show(io::IO, ::BotElement) = print(io, "⊥")

<=(::BotElement, ::TopElement) = true
<=(::BotElement, ::LatticeElement) = true
<=(::LatticeElement, ::TopElement) = true

# join
⊔(x::LatticeElement, y::LatticeElement) = (x <= y ? y : y <= x ? x : ⊤)

# meet
⊓(x::LatticeElement, y::LatticeElement) = (x <= y ? x : y <= x ? y : ⊥)

# Note: the above definitions are such that we get flat lattices
# "for free" by wrapping any simple julia value in an immutable
# LatticeElement.


# Part 3: abstract value

# Note: the paper (https://api.semanticscholar.org/CorpusID:28519618) uses U+1D56E MATHEMATICAL BOLD FRAKTUR CAPITAL C for this
const AbstractValue = Dict{Symbol,LatticeElement}

# Here we extend lattices of values to lattices of mappings of variables
# to values. meet and join operate elementwise, and from there we only
# need equality on dictionaries to get <= and <.

⊔(X::AbstractValue, Y::AbstractValue) = AbstractValue( v => X[v] ⊔ Y[v] for v in keys(X) )
⊓(X::AbstractValue, Y::AbstractValue) = AbstractValue( v => X[v] ⊓ Y[v] for v in keys(X) )

<=(X::AbstractValue, Y::AbstractValue) = X⊓Y == X
<(X::AbstractValue, Y::AbstractValue)  = X<=Y && X!=Y


#########################################################
# example problem 1. - find uses of undefined variables #
#########################################################

# flat lattice of variable definedness

struct IsDefined <: LatticeElement
    is::Bool
end
show(io::IO, isdef::IsDefined) = print(io, isdef.is ? "defined" : "undefined")

const undef = IsDefined(false)
const def   = IsDefined(true)

# abstract semantics

abstract_eval(x::Sym, s::AbstractValue) = get(s, x.name, ⊥)

abstract_eval(x::Num, s::AbstractValue) = def

function abstract_eval(x::Call, s::AbstractValue)
    if any(a->(abstract_eval(a,s) == ⊥), x.args)
        return ⊥
    end
    return def
end

# data flow analysis

# Note:
# - in this problem, we make sure that states will always move to higher position in lattice, so we use ⊔ (join) operator for state update
# - and the condition we use to check whether or not the statement makes a change is `!(new <= prev)`
function max_fixed_point(P::Program, a₁::AbstractValue, eval) where {Program<:AbstractVector{Stmt}}
    n = length(P)
    bot = AbstractValue( v => ⊥ for v in keys(a₁) )
    s = [ a₁; [ bot for i = 2:n ] ]
    W = BitSet(1:n)

    while !isempty(W)
        pc = first(W)
        while pc != n+1
            delete!(W, pc)
            I = P[pc]
            new = s[pc]
            if isa(I, Assign)
                # for an assignment, outgoing value is different from incoming
                new = copy(new)
                new[I.lhs.name] = eval(I.rhs, new)
            end
            if isa(I, Goto)
                pc´ = I.label
            else
                pc´ = pc+1
                if isa(I, GotoIf)
                    l = I.label
                    if !(new <= s[l])
                        push!(W, l)
                        s[l] = s[l] ⊔ new
                    end
                end
            end
            if pc´<=n && !(new <= s[pc´])
                s[pc´] = s[pc´] ⊔ new
                pc = pc´
            else
                pc = n+1
            end
        end
    end
    s
end

prog1 = [Assign(:x, 0),                       # 1
         GotoIf(5, Call(:randbool, Exp[])),   # 2
         Assign(:y, 1),                       # 3
         Goto(5),                             # 4
         Assign(:z, Call(:pair, Exp[:x,:y])), # 5
         Ret()]

# variables initially undefined
l = AbstractValue(:x => undef, :y => undef, :z => undef)

max_fixed_point(prog1, l, abstract_eval)


#########################################################################
# example problem 2. - constant folding propagation (the paper example) #
#########################################################################

# lattice

# Note: intuitively, each lattice element can be interpreted in the following way:
# - `Int` means "constant" value
# - `⊤` means "not constant due to missing information"
# - `⊥` means "not constant due to conflict"

struct Const <: LatticeElement
    val::Int
end

# abstract semantics

abstract_eval(x::Num, s::AbstractValue) = Const(x.val)

abstract_eval(x::Sym, s::AbstractValue) = get(s, x.name, ⊤)

function abstract_eval(x::Call, s::AbstractValue)
    f = getfield(@__MODULE__, x.head.name)

    argvals = Int[]
    for arg in x.args
        arg = abstract_eval(arg, s)
        arg === ⊥ && return ⊥ # bail out if any of call arguments is non-constant
        push!(argvals, unwrap_val(arg))
    end

    return Const(f(argvals...))
end

# unwrap our lattice representation into actual Julia value
unwrap_val(x::Num)   = x.val
unwrap_val(x::Const) = x.val

# Note: in this problem, we make sure that states will always move to _lower_ position in lattice, so
# - initialize states with `⊤`
# - we use `⊓` (meet) operator to update states,
# - and the condition we use to check whether or not the statement makes a change is `!(new >= prev)`
function max_fixed_point(P::Program, a₁::AbstractValue, eval) where {Program<:AbstractVector{Stmt}}
    n = length(P)
    top = AbstractValue( v => ⊤ for v in keys(a₁) )
    s = [ a₁; [ top for i = 2:n ] ]
    W = BitSet(1:n)

    while !isempty(W)
        pc = first(W)
        while pc != n+1
            delete!(W, pc)
            I = P[pc]
            new = s[pc]
            if isa(I, Assign)
                # for an assignment, outgoing value is different from incoming
                new = copy(new)
                new[I.lhs.name] = eval(I.rhs, new)
            end
            if isa(I, Goto)
                pc´ = I.label
            else
                pc´ = pc+1
                if isa(I, GotoIf)
                    l = I.label
                    if !(new >= s[l])
                        push!(W, l)
                        s[l] = s[l] ⊓ new
                    end
                end
            end
            if pc´<=n && !(new >= s[pc´])
                s[pc´] = s[pc´] ⊓ new
                pc = pc´
            else
                pc = n+1
            end
        end
    end
    s
end

prog1 = [Assign(:x, 1),                    # 1
         Assign(:y, 2),                    # 2
         Assign(:z, 3),                    # 3
         Goto(9),                          # 4
         Assign(:r, Call(:(+), [:y, :z])), # 5
         GotoIf(8, Call(:(≤), [:x, :z])),  # 6
         Assign(:r, Call(:(+), [:z, :y])), # 7
         Assign(:x, Call(:(+), [:x, 1])),  # 8
         GotoIf(5, Call(:(<), [:x, 10])),  # 9
         ]

# initially values are not constant (due to missing information)
a₁ = AbstractValue(:x => ⊤, :y => ⊤, :z => ⊤, :r => ⊤)

max_fixed_point(prog1, a₁, abstract_eval) # The solution contains the `:r => Const(5)`, which is not found in the program
