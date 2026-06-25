include("Cats.jl");     using .Cats
include("Adjoints.jl"); using .Adjoints

# NATS AS A POSET
# Objects: natural numbers.  Morphism (m,n): a witness that m ≤ n.
# This is different from nats_cat (which is ℕ as a monoid/one-object category).
nats_pos  = Cat(
    pair -> pair[1],
    pair -> pair[2],
    n    -> (n, n),
    (f, g) -> (f[1], g[2])
)
nats_pdcat = DecidableCat(nats_pos, (m,n) -> m==n, (f,g) -> f==g)

## ADJUNCTION: ×2 ⊣ ⌊÷2⌋
#
# L = ×2  :  n ↦ 2n,    (m≤n) ↦ (2m≤2n)
# R = ⌊÷2⌋ : n ↦ n÷2,  (m≤n) ↦ (m÷2≤n÷2)
#
# Galois connection:  2m ≤ n  ↔  m ≤ ⌊n/2⌋
#
# Unit   η_n : n  →  ⌊2n/2⌋ = n      (identity morphism, n ≤ n)
# Counit ε_n : 2⌊n/2⌋ → n            (valid since 2⌊n/2⌋ ≤ n)

double = Func(nats_pos, nats_pos,
    n    -> 2n,
    pair -> (2*pair[1], 2*pair[2]))

half = Func(nats_pos, nats_pos,
    n    -> n÷2,
    pair -> (pair[1]÷2, pair[2]÷2))

unit_η   = NatTrans(func_id(nats_pos), func_comp(double, half),
                    n -> (n, n))                  # n ≤ ⌊2n/2⌋ = n

counit_ε = NatTrans(func_comp(half, double), func_id(nats_pos),
                    n -> (2*(n÷2), n))            # 2⌊n/2⌋ ≤ n

adj = Adjunction(double, half, unit_η, counit_ε)

for n in 0:9
    @assert check_triangle_left(adj,  nats_pdcat, n)
    @assert check_triangle_right(adj, nats_pdcat, n)
end
println("×2 ⊣ ⌊÷2⌋ adjunction on ℕ poset: triangles hold for 0..9")
