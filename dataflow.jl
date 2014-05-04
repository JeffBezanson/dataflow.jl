# Part 1: programs

import Base: convert

abstract Stmt

abstract Exp <: Stmt

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

# 2.1. partial order, meet, join, top, bottom, and their identities

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

join(x::LatticeElement, y::LatticeElement) = (x <= y ? y : y <= x ? x : ⊤)
meet(x::LatticeElement, y::LatticeElement) = (x <= y ? x : y <= x ? y : ⊥)

# 2.2. flat lattice of variable definedness

immutable IsDefined <: LatticeElement
    is::Bool
end

convert(::Type{IsDefined}, x::Num) = IsDefined(true)

# Note: the above definitions are such that we get flat lattices
# "for free" by wrapping any simple julia value in an immutable
# LatticeElement.


# Part 3: dataflow analysis

# Note: the paper uses U+1D56E MATHEMATICAL BOLD FRAKTUR CAPITAL C for this
typealias AbstractValue Dict{Symbol,LatticeElement}

# Here we extend lattices of values to lattices of mappings of variables
# to values. meet and join operate elementwise, and from there we only
# need equality on dictionaries to get <= and <.

meet(X::AbstractValue, Y::AbstractValue) =
    (Symbol=>LatticeElement)[ v => meet(X[v],Y[v]) for v in keys(X) ]

join(X::AbstractValue, Y::AbstractValue) =
    (Symbol=>LatticeElement)[ v => join(X[v],Y[v]) for v in keys(X) ]

<=(X::AbstractValue, Y::AbstractValue) = meet(X,Y)==X
< (X::AbstractValue, Y::AbstractValue) = X!=Y && X<=Y

immutable Env
    locals::AbstractValue
    funcs::Dict{Symbol,Function}
end

function max_fixed_point{T<:LatticeElement}(P::Vector, env::Env, L::Type{T})
    a₁ = env.locals
    n = length(P)
    s = [ (Symbol=>LatticeElement)[ v => ⊥ for v in keys(a₁) ] for i = 1:n ]
    s[1] = a₁
    W = IntSet(1)

    while !isempty(W)
        pc = first(W)
        while pc != n+1
            delete!(W, pc)
            Ipc = P[pc]
            new = semantics(Ipc, Env(s[pc], env.funcs), L)
            if isa(Ipc, Goto)
                pc´ = Ipc.label
            else
                pc´ = pc+1
                if isa(Ipc, GotoIf)
                    l = Ipc.label
                    if !(new <= s[l])
                        push!(W, l)
                        s[l] = join(s[l], new)
                    end
                end
            end
            if pc´<=n && !(new <= s[pc´])
                s[pc´] = join(s[pc´], new)
                pc = pc´
            else
                pc = n+1
            end
        end
    end
    s
end

semantics(x, e::Env, L) = e.locals

function semantics(x::Assign, e::Env, L)
    v = abstract_eval(x.rhs, e, L)
    s = copy(e.locals)
    s[x.lhs.name] = v
    return s
end

abstract_eval(x::Sym, e::Env, L) = get(e.locals, x.name, ⊥)

abstract_eval(x::Num, e::Env, L) = convert(L, x)

function abstract_eval(x::Call, e::Env, L)
    if !haskey(e.funcs, x.head.name)
        return ⊥
    end
    args = map(a->abstract_eval(a, e, L), {x.args...})
    if any(x->(x == ⊥), args)
        return ⊥
    end
    e.funcs[x.head.name](args...)
end


# example problem

prog1 = {Assign(:x, 0),                       # 1
         GotoIf(5, Call(:randbool, Exp[])),   # 2
         Assign(:y, 1),                       # 3
         Goto(5),                             # 4
         Assign(:z, Call(:pair, Exp[:x,:y])), # 5
         Ret()}

l = (Symbol=>LatticeElement)[:x => IsDefined(false),
                             :y => IsDefined(false),
                             :z => IsDefined(false)]

funcs = [:randbool => (a...)->IsDefined(true),
         :pair     => (a...)->IsDefined(true)]

max_fixed_point(prog1, Env(l, funcs), IsDefined)
