# Fin.jl — the category of finite sets (skeleton)
#
# Objects are natural numbers n (representing the set {0,...,n-1}).
# Morphisms n → m are functions represented as lookup tables (length-n
# vectors with entries in 0:m-1). Composition is function composition
# via table indexing.
#
# Provides fin_cat (Cat) and fin_dcat (DecidableCat), and the helper
# functions compose_fin and eq_fin used to build them.

module Fin

using ..Cats

export FinMorphism, compose_fin, eq_fin, fin_cat, fin_dcat
export prod_obj, prod_mor, coprod_obj, coprod_mor
export terminal_obj, terminal_mor
export exp_obj, exp_mor, eval_mor, curry

struct FinMorphism
    dom   :: Int
    cod   :: Int
    table :: Vector{Int}   # length dom, entries in 0:cod-1
end

compose_fin(f::FinMorphism, g::FinMorphism) =
    FinMorphism(f.dom, g.cod, g.table[f.table .+ 1])

eq_fin(f::FinMorphism, g::FinMorphism) =
    f.dom == g.dom && f.cod == g.cod && f.table == g.table

fin_cat  = Cat(f -> f.dom, f -> f.cod,
               n -> FinMorphism(n, n, collect(0:n-1)), compose_fin)
fin_dcat = DecidableCat(fin_cat, (m,n) -> m==n, eq_fin)

# Cartesian structure for fin_cat.
# prod_obj and prod_mor implement the product functor × : C×C → C.
# For categories without products, calling these will give a MethodError.
# Objects: n × m = n*m  (row-major encoding: (i,j) ↦ i*m + j)
prod_obj(C::AbstractCat, n::Int, m::Int) = n * m

# Morphisms: (f×g)(i*m+j) = f(i)*g.cod + g(j)
function prod_mor(C::AbstractCat, f::FinMorphism, g::FinMorphism)
    n, m, q = f.dom, g.dom, g.cod
    FinMorphism(n*m, f.cod*q,
        [f.table[k÷m + 1] * q + g.table[k%m + 1] for k in 0:n*m-1])
end

# Cocartesian structure for fin_cat.
# coprod_obj and coprod_mor implement the coproduct functor + : C×C → C.
# For categories without coproducts, calling these will give a MethodError.
# Objects: n + m = n+m  (disjoint union: left half 0:n-1, right half n:n+m-1)
coprod_obj(C::AbstractCat, n::Int, m::Int) = n + m

# Morphisms: (f+g)(k) = f(k) for k < n, p + g(k-n) for k ≥ n
function coprod_mor(C::AbstractCat, f::FinMorphism, g::FinMorphism)
    n, p = f.dom, f.cod
    FinMorphism(n + g.dom, p + g.cod,
        [[f.table[k+1]       for k in 0:n-1];
         [p + g.table[k+1]   for k in 0:g.dom-1]])
end

# Terminal object for fin_cat: the one-element set {0}
terminal_obj(C::AbstractCat)          = 1
terminal_mor(C::AbstractCat, n::Int)  = FinMorphism(n, 1, fill(0, n))

# Exponential object: m^n = set of functions n → m
# Encoding: function f is the integer k = Σ f(i)*m^(n-1-i)  (big-endian base m)
exp_obj(C::AbstractCat, n::Int, m::Int) = m^n

_encode(table, n::Int, m::Int) = sum(table[i+1] * m^(n-1-i) for i in 0:n-1; init=0)
_decode(k::Int, i::Int, n::Int, m::Int) = (k ÷ m^(n-1-i)) % m

# Evaluation morphism: eval : m^n × n → m
# (k,i) encoded as k*n+i (row-major);  eval(k,i) = f_k(i)
function eval_mor(C::AbstractCat, n::Int, m::Int)
    mn = m^n
    FinMorphism(mn*n, m,
        [_decode(k, i, n, m) for k in 0:mn-1 for i in 0:n-1])
end

# Exponential morphism: h^n : a^n → b^n,  f : n→a  ↦  h∘f : n→b
function exp_mor(C::AbstractCat, n::Int, h::FinMorphism)
    a, b = h.dom, h.cod
    FinMorphism(a^n, b^n,
        [_encode([h.table[_decode(k,i,n,a)+1] for i in 0:n-1], n, b) for k in 0:a^n-1])
end

# Curry: f : a×n → m  →  curry(f) : a → m^n
# curry(f)(av) encodes the function  i ↦ f(av*n + i)
function curry(C::AbstractCat, f::FinMorphism, n::Int)
    a, m = f.dom ÷ n, f.cod
    FinMorphism(a, m^n,
        [_encode([f.table[av*n + i + 1] for i in 0:n-1], n, m) for av in 0:a-1])
end

end # module Fin
