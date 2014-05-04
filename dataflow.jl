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
    head::Exp
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
    e::Exp
end

convert(::Type{Exp}, s::Symbol) = Sym(s)
convert(::Type{Sym}, s::Symbol) = Sym(s)
convert(::Type{Exp}, n::Int)    = Num(n)
convert(::Type{Num}, n::Int)    = Num(n)

prog1 =
    {Assign(:x, 0),                      # 1
     GotoIf(4, Call(:randbool, Exp[])),  # 2
     Assign(:y, 1),                      # 3
     Ret(Call(:pair, Exp[:x,:y]))        # 4
     }


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

join(x::LatticeElement, y::LatticeElement) = (x == y ? x : ⊤)
meet(x::LatticeElement, y::LatticeElement) = (x == y ? x : ⊥)

<=(::BotElement, ::TopElement) = true
<=(::BotElement, ::LatticeElement) = true
<=(::LatticeElement, ::TopElement) = true

join(::BotElement, ::TopElement) = ⊤
join(::TopElement, ::BotElement) = ⊤

meet(::BotElement, ::TopElement) = ⊥
meet(::TopElement, ::BotElement) = ⊥

# 2.2. flat lattice of variable definedness

immutable IsDefined <: LatticeElement
    is::Bool
end

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

function max_fixed_point(P::Vector, a₁::AbstractValue)
    n = length(P)
    s = [ (Symbol=>LatticeElement)[ v => ⊥ for v in keys(a₁) ] for i = 1:n ]
    s[1] = a₁
    W = IntSet(1)

    while !isempty(W)
        pc = first(W)
        while pc != n+1
            delete!(W, pc)
            Ipc = P[pc]
            new = semantics(Ipc, s[pc])
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
            if !(new <= s[pc´])
                s[pc´] = join(s[pc´], new)
                pc = pc´
            else
                pc = n+1
            end
        end
    end
    s
end
