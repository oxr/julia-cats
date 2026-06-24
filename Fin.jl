module Fin

using .Cats

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
