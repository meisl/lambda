#### Super-fast intro to (pure) Lambda calculus:

Given some (possibly infinite) set `V` of symbols ("variables"),
the set of λ-terms ("Lambda-terms") is defined as:
* every `x` &isin; `V` is a λ-term
* if both, `f` and `t` are λ-terms, then `(f t)` is a λ-term ("Application")
* if `x` &isin; `V` and `t` is a λ-term, then `(λx.t)` is a λ-term ("Abstraction")

Well, that's all about it! ...at least for the syntax :)

Note that `f` and `t`, or, `x` and `t` mentioned in the last two pts, respectively, need not be distinct.

Also note that we silently assumed that none of the following special characters is &isin; `V`, 
ie. that none of these are valid symbols in themselves: `λ`, `.`, `(`, `)` and ` ` (whitespace).

OK, so far it's really nothing else but just that: syntax.
But, as you will guess, we can attach meaning to it - in a quite straightforward manner.


##### Let's start bottom-up, with Abstraction, `(λx.t)`:
This is intended to denote *functions*.
Eg `(λx.x)` would be the identity function - whatever you pass in you'll get back.
Different is `(λx.y)` which *always* gives you back `y`, no matter what's passed in.


##### Next comes Application, `(f t)`:
This is intended to capture the meaning of "applying a function".
Recall that `f` is required to be a λ-term (that is, NOT restricted to variables).

It could, for example, be the identity function `(λx.x)`, as in `((λx.x) t)`.
Of course, the result of applying the identity function `t` - is just `t`.

What about `((λx.y) t)`? Well, as we said before, `(λx.y)` always gives you back `y`, no matter what's passed in.
Hence, the result of this application is `y` (whatever *that* is, we simply don't care).


##### Finally, single variables like `x`:
...

