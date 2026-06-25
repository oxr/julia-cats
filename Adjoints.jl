# Adjoints.jl — adjunctions between categories
#
# An adjunction F ⊣ G is given in the unit-counit presentation:
#   left   F : C → D
#   right  G : D → C
#   unit   η : Id_C ⇒ G∘F
#   counit ε : F∘G ⇒ Id_D
#
# Triangle identities (diagrammatic order):
#   left  triangle: F(η_a) ; ε_{F(a)} = id_{F(a)}   for all a : Obj(C)
#   right triangle: η_{G(b)} ; G(ε_b) = id_{G(b)}   for all b : Obj(D)
#
# The induced monad G∘F (with unit η and mult G(ε_F)) can be built
# once a Monad struct is defined.

module Adjoints

using ..Cats
using ..Functors

export Adjunction, check_triangle_left, check_triangle_right

struct Adjunction
    left   :: Func      # F : C → D
    right  :: Func      # G : D → C
    unit   :: NatTrans  # η : Id_C ⇒ G∘F
    counit :: NatTrans  # ε : F∘G ⇒ Id_D
end

# left triangle: F(η_a) ; ε_{F(a)} = id_{F(a)}
function check_triangle_left(A::Adjunction, D::AbstractDecidableCat, a)
    α = vcomp(hcomp_right(A.unit, A.left), hcomp_left(A.left, A.counit), D)
    hom_eq(D, α.component(a), id(D, A.left.obj_map(a)))
end

# right triangle: η_{G(b)} ; G(ε_b) = id_{G(b)}
function check_triangle_right(A::Adjunction, C::AbstractDecidableCat, b)
    α = vcomp(hcomp_left(A.right, A.unit), hcomp_right(A.counit, A.right), C)
    hom_eq(C, α.component(b), id(C, A.right.obj_map(b)))
end

end # module Adjoints
