# Part 1: programs

import Base: convert

abstract Exp

immutable Sym <: Exp
    name::Symbol
end

immutable Num <: Exp
    val::Int
end

type Call <: Exp
    head::Sym
    args::Vector{Exp}
end

abstract Stmt

type Assign <: Stmt
    lhs::Sym
    rhs::Exp
end

type Goto <: Stmt
    label::Int
end

type GotoIf <: Stmt
    label::Int
    cond::Exp
end

type Ret <: Stmt
end

convert(::Type{Exp}, s::Symbol) = Sym(s)
convert(::Type{Sym}, s::Symbol) = Sym(s)
convert(::Type{Exp}, n::Int)    = Num(n)
convert(::Type{Num}, n::Int)    = Num(n)


# Part 2: lattices

# partial order, meet, join, top, bottom, and their identities

import Base: <=, ==, <, show

abstract LatticeElement

# Note: == and < are defined such that future LatticeElements only
# need to implement <=

<=(x::LatticeElement, y::LatticeElement) = x===y

==(x::LatticeElement, y::LatticeElement) = x<=y && y<=x

<(x::LatticeElement, y::LatticeElement) = x<=y && !(y<=x)

immutable TopElement <: LatticeElement; end
immutable BotElement <: LatticeElement; end

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


# Part 3: dataflow analysis

# Note: the paper uses U+1D56E MATHEMATICAL BOLD FRAKTUR CAPITAL C for this
typealias AbstractValue Dict{Symbol,LatticeElement}

# Here we extend lattices of values to lattices of mappings of variables
# to values. meet and join operate elementwise, and from there we only
# need equality on dictionaries to get <= and <.

⊔(X::AbstractValue, Y::AbstractValue) = [ v => X[v] ⊔ Y[v] for v in keys(X) ]
⊓(X::AbstractValue, Y::AbstractValue) = [ v => X[v] ⊓ Y[v] for v in keys(X) ]

<=(X::AbstractValue, Y::AbstractValue) = X⊓Y == X
< (X::AbstractValue, Y::AbstractValue) = X!=Y && X<=Y

function max_fixed_point(P::Vector, a₁::AbstractValue, eval)
    n = length(P)
    bot = AbstractValue([ v => ⊥ for v in keys(a₁) ])
    s = [ a₁; [ bot for i = 2:n ] ]
    W = IntSet(1)

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


# example problem - find uses of undefined variables

# flat lattice of variable definedness

immutable IsDefined <: LatticeElement
    is::Bool
end

const undef = IsDefined(false)
const def   = IsDefined(true)

abstract_eval(x::Sym, s::AbstractValue) = get(s, x.name, ⊥)

abstract_eval(x::Num, s::AbstractValue) = def

function abstract_eval(x::Call, s::AbstractValue)
    if any(a->(abstract_eval(a,s) == ⊥), x.args)
        return ⊥
    end
    return def
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
