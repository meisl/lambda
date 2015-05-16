# ~> Compile Error: unbound variables y, z, w, u
#(λx.λ_.y (x λy.x y z w)) "fo\noö" "bar" "baz" λy.u "qumbl"

# ~> (Runtime) ERROR: cannot apply "xfo\noö" to λy.x y
#(λx.λ_.(x λy.x y)) "xfo\noö" "xbar" "xbaz" λz."qumbl"

# K applied to "foo" and something: ~> "foo"
#(λx.λ_.x) "foo" (λf.λg.λx.f (g x))

# Turing's Y:
#(λU.U U) (λu.λf.f (u u f))

# Turing's Y applied to a function that ignores param self:
#(λU.U U) (λu.λf.f (u u f)) (λself.λx.x)

#(λy.λz.λx.y (λy.y z)) "y" "z"


# Lists:
(λnil.λcons.λcar.λcdr.
    (λxs.
        #nil
        #car xs              # "a"
        #car nil             # ~> (Runtime) ERROR: cannot apply "car" to "nil"
        #cdr xs              # (cons "b" (cons "c" nil))
        #car (cdr xs)        # "b"
        cdr (cdr xs)        # (cons "c", nil)
        #car (cdr (cdr xs))  # "c"
    ) (cons "a" (cons "b" (cons "c" nil)))
)
    (λonNil.λonCons.onNil)                  # ctor nil
    (λx.λxs.λonNil.λonCons.onCons x xs)     # ctor cons
    (λxs.xs ("car" "nil") (λhd.λtl.hd))     # car   (provoke error on nil)
    (λxs.xs ("cdr" "nil") (λhd.λtl.tl))     # cdr   (provoke error on nil)
