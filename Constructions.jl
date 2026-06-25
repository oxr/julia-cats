# Constructions.jl — standard constructions on categories
#
# Each construction is defined twice via multiple dispatch:
# once for Cat (the underlying structure) and once for DecidableCat
# (which threads through the appropriate equality witnesses).
# This avoids duplicating logic — only the equality wiring differs.
#
#   op_cat      — opposite category C^op (dom/cod swapped, comp reversed)
#   prod_cat    — product category C × D (objects and morphisms are pairs)
#   slice_cat   — slice category C/x (objects are legs f:a→x, morphisms are
#                 triangles h:a→b with h;g=f); morphisms are boxed in SliceMor
#                 to carry the domain and codomain legs alongside h
#   coslice_cat — coslice x/C, defined as slice_cat(op_cat(C), x)

module Constructions

using ..Cats

export op_cat, prod_cat, slice_cat, coslice_cat, SliceMor

## OPPOSITE CATEGORY
function op_cat(C::Cat)
    Cat(
        f -> C.cod(f),
        f -> C.dom(f),
        x -> C.id(x),
        (f, g) -> C.comp(g, f)
    )
end

function op_cat(DC::DecidableCat)
    DecidableCat(op_cat(DC.cat), DC.obj_eq, DC.hom_eq)
end

## PRODUCT CATEGORY C × D
# objects are pairs (a, b), morphisms are pairs (f, g)
function prod_cat(C::Cat, D::Cat)
    Cat(
        fg -> (C.dom(fg[1]), D.dom(fg[2])),
        fg -> (C.cod(fg[1]), D.cod(fg[2])),
        ab -> (C.id(ab[1]), D.id(ab[2])),
        (fg, hk) -> (C.comp(fg[1], hk[1]), D.comp(fg[2], hk[2]))
    )
end

function prod_cat(DC::DecidableCat, DD::DecidableCat)
    DecidableCat(
        prod_cat(DC.cat, DD.cat),
        (ab, cd) -> DC.obj_eq(ab[1], cd[1]) && DD.obj_eq(ab[2], cd[2]),
        (fg, hk) -> DC.hom_eq(fg[1], hk[1]) && DD.hom_eq(fg[2], hk[2])
    )
end

## SLICE CATEGORY C/x
# objects: morphisms f : a → x in C
# morphisms f → g: h : a → b in C such that h ; g = f (diagrammatic)

# morphisms in the slice category must be boxed
# because they must carry the domain and codomain of the morphism in the slice category,
struct SliceMor
    dom :: Any  # f : a → x
    cod :: Any  # g : b → x
    mor :: Any  # h : a → b in C
end

function slice_cat(C::Cat, x)
    Cat(
        sm -> sm.dom,
        sm -> sm.cod,
        f  -> SliceMor(f, f, id(C, C.dom(f))),
        (sm1, sm2) -> SliceMor(sm1.dom, sm2.cod, comp(C, sm1.mor, sm2.mor))
    )
end

function slice_cat(DC::DecidableCat, x)
    DecidableCat(
        slice_cat(DC.cat, x),
        DC.hom_eq,
        (sm1, sm2) -> DC.hom_eq(sm1.mor, sm2.mor)
    )
end

## COSLICE CATEGORY x/C = slice of opposite
coslice_cat(C::Cat, x)           = slice_cat(op_cat(C), x)
coslice_cat(DC::DecidableCat, x) = slice_cat(op_cat(DC), x)

end # module Constructions
