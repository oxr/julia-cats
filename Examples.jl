include("Cats.jl");          using .Cats
include("Fin.jl");           using .Fin
include("Constructions.jl"); using .Constructions
include("Grothendieck.jl");  using .Grothendieck

## NATS: natural numbers as a one-object category, composition is addition
nats_cat = Cat(
    f -> :N, f -> :N,
    x -> 0,
    (m, n) -> m + n
)
nats = DecidableCat(nats_cat, (x,y) -> x==y, (m,n) -> m==n)

@assert check_unitl(nats, 3)
@assert check_unitr(nats, 5)
@assert check_assoc(nats, 1, 2, 3)

## FIN: skeleton of finite sets (from Fin.jl)
f32 = FinMorphism(3, 2, [0, 1, 0])   # {0,1,2} → {0,1}
g23 = FinMorphism(2, 3, [0, 2])      # {0,1} → {0,1,2}
h31 = FinMorphism(3, 1, [0, 0, 0])   # {0,1,2} → {0}

@assert check_unitl(fin_dcat, f32)
@assert check_unitr(fin_dcat, f32)
@assert check_assoc(fin_dcat, f32, g23, h31)

## FUNCTOR: doubling on nats  F(n) = 2n, preserves + and 0
double = Func(nats_cat, nats_cat, x -> x, n -> 2n)

@assert check_func_id(double, nats, nats, :N)     # F(0) = 0
@assert check_func_comp(double, nats, nats, 3, 4) # F(3+4) = F(3)+F(4)

## NAT TRANS: shift by k is a nat trans id_nats ⇒ id_nats
# naturality: k + m = m + k  (holds since + is commutative)
id_nats = func_id(nats_cat)
shift5  = NatTrans(id_nats, id_nats, x -> 5)
shift3  = NatTrans(id_nats, id_nats, x -> 3)

@assert check_naturality(shift5, nats_cat, nats, 7)

shift8 = vcomp(shift5, shift3, nats)
@assert nats.hom_eq(shift8.component(:N), 8)
@assert check_naturality(shift8, nats_cat, nats, 7)

## OPPOSITE: nats^op  (same as nats since + is commutative)
nats_op = op_cat(nats)
@assert check_unitl(nats_op, 4)
@assert check_assoc(nats_op, 1, 2, 3)

## PRODUCT: nats × nats, morphisms are pairs of naturals
nats2 = prod_cat(nats, nats)
@assert nats2.hom_eq(
    nats2.cat.comp((1, 2), (3, 4)),
    (4, 6))

## SLICE: fin_cat / 2
# objects: functions n → 2  (i.e., binary predicates on {0,...,n-1})
# morphism f → g: h such that h ; g = f
sl = slice_cat(fin_dcat, 2)

f_leg = FinMorphism(3, 2, [0, 1, 0])
g_leg = FinMorphism(2, 2, [1, 0])
h_mor = FinMorphism(3, 2, [1, 0, 1])

sm = SliceMor(f_leg, g_leg, h_mor)

@assert check_unitl(sl, sm)
@assert check_unitr(sl, sm)

## GROTHENDIECK: Z/2Z action on nats
z2_action = SetFunctor(
    nats_cat,
    x  -> (0, 1),
    n  -> (x -> (x + n) % 2)
)

E  = grothendieck(z2_action, nats, (x,y) -> x==y)
o0 = GObj(:N, 0)
o1 = GObj(:N, 1)

@assert check_unitl(E, GMor(o0, o1, 1))
@assert check_assoc(E, GMor(o0, o1, 1), GMor(o1, o0, 3), GMor(o0, o1, 5))
