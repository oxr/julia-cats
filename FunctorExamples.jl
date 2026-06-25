include("Cats.jl");     using .Cats

Δ(C) = Func(
            C, 
            prod_cat(C,C), 
            x -> (x,x), 
            f -> ((x,y) -> (f(x),f(y))
)