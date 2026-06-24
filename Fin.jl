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

end # module Fin
