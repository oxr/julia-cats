include("Grothendieck.jl")
include("Fin.jl")

## Z/2Z action on nats
# F(:N) = {0,1},  F(n)(x) = (x+n) mod 2
# morphisms (:N,x)→(:N,y): naturals n with (x+n)%2 = y

nats_cat  = Cat(f -> :N, f -> :N, x -> 0, (m,n) -> m+n)
nats      = DecidableCat(nats_cat, (x,y) -> x==y, (m,n) -> m==n)

z2_action = SetFunctor(
    nats_cat,
    x -> (0, 1),
    n -> (x -> (x + n) % 2)
)

E  = grothendieck(z2_action, nats, (x,y) -> x==y)
o0 = GObj(:N, 0)
o1 = GObj(:N, 1)

@assert check_unitl(E, GMor(o0, o1, 1))
@assert check_assoc(E, GMor(o0, o1, 1), GMor(o1, o0, 3), GMor(o0, o1, 5))

## Underlying elements functor U : Fin → Set
# U(n) = {0,...,n-1},   U(f)(i) = f.table[i+1]
# objects (n,i) = "element i of finite set n"
# morphisms (n,i)→(m,j): FinMorphisms f:n→m with f(i)=j

U  = SetFunctor(
    fin_cat,
    n -> 0:n-1,
    f -> (i -> f.table[i + 1])
)

EU   = grothendieck(U, fin_dcat, (i,j) -> i==j)
e3_1 = GObj(3, 1)
e2_0 = GObj(2, 0)
e1_0 = GObj(1, 0)

m_a = GMor(e3_1, e2_0, FinMorphism(3, 2, [1, 0, 1]))  # f(1)=0 ✓
m_b = GMor(e2_0, e1_0, FinMorphism(2, 1, [0, 0]))      # g(0)=0 ✓
m_c = GMor(e1_0, e1_0, FinMorphism(1, 1, [0]))

@assert check_unitl(EU, m_a)
@assert check_unitr(EU, m_a)
@assert check_assoc(EU, m_a, m_b, m_c)
