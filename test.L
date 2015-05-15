# ~> Compile Error: unbound variables y, z, w, u
#(λx.λ_.y (x λy.x y z w)) "fo\noö" "bar" "baz" λy.u "qumbl"

# ~> (Runtime) ERROR: cannot apply "xfo\noö" to λy.x y
#(λx.λ_.(x λy.x y)) "xfo\noö" "xbar" "xbaz" λz."qumbl"

# K applied to "foo" and "bar": ~> "foo"
#(λx.λ_.x) "foo" "bar"

# Turing's Y:
(λU.U U) (λu.λf.f (u u f))

# Turing's Y applied to a function that ignores param self:
#(λU.U U) (λu.λf.f (u u f)) (λself.λx.x)

#(λy.λz.λx.y (λy.y z)) "y" "z"

