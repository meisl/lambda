# ~> Compile Error: unbound variables y, z, w, u
#(λx.λ_.y (x λy.x y z w)) "fo\noö" "bar" "baz" λy.u "qumbl"

# ~> (Runtime) ERROR: cannot apply "xfo\noö" to λy.x y
#(λx.λ_.(x λy.x y)) "xfo\noö" "xbar" "xbaz" λz."qumbl"

#(λy.λz.λx.y (λy.y z)) "y" "z"

# K applied to "foo" and something: ~> "foo"
#(λx.λ_.x) "foo" (λf.λg.λx.f (g x))

# Turing's Y:
#(λU.U U) (λu.λf.f (u u f))

# Turing's Y applied to a function that ignores param self:
#(λU.U U) (λu.λf.f (u u f)) (λself.λx.x)


(λU.λM.λC.λB.λS.λK.λI.
    (λY.
        # Lists:
        (λnil.λcons.λcar.λcdr.λfoldl.
            (λxs.
                #nil
                #car xs              # "a"
                #car nil             # ~> (Runtime) ERROR: cannot apply "car" to "nil"
                #cdr xs              # (cons "b" (cons "c" nil))
                #car (cdr xs)        # "b"
                #cdr (cdr xs)        # (cons "c", nil)
                #car (cdr (cdr xs))  # "c"
                #foldl (λx.λ_.x) "zzz" xs   # "zzz"
                #foldl (λ_.λx.x) "zzz" xs   # "c"
                #foldl
                #Y
                #(λy.λx.λzzz.x y x) "foo" ((λx.λu.u x) ((λa.λb.λ_.a b) "bar" "qumbl"))
                "foo" "bar"
            ) (cons "a" (cons "b" (cons "c" nil)))
        )
        (λonNil.λonCons.onNil)                  # ctor nil
        (λx.λxs.λonNil.λonCons.onCons x xs)     # ctor cons
        (λxs.xs ("car" "nil") (λhd.λtl.hd))     # car   (provoke error on nil)
        (λxs.xs ("cdr" "nil") (λhd.λtl.tl))     # cdr   (provoke error on nil)
        (Y λself.λf.λstart.λxs.                 # foldl
            xs start
               λhd.λtl.self f (f start hd) tl
        )
    )
    (U U)   # Y
)
(λu.λf.f (u u f))       # U
(λx.x x)                # M
(λf.λx.λy.f y x)        # C
(λf.λg.λx.f (g x))      # B
(λf.λg.λx.f x (g x))    # S
(λx.λ_.x)               # K
(λx.x)                  # I
