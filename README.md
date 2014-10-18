### An intro to (pure) Lambda calculus:


#### λ-terms

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


#### What should λ-terms *mean*? (interpreting them, "semantics")

##### Let's start bottom-up, with Abstraction, `(λx.t)`:
This is intended to denote *functions*.
Eg `(λx.x)` would be the identity function - whatever you pass in you'll get back.
Different is `(λx.y)` which *always* gives you back `y`, no matter what's passed in.


##### Next comes Application, `(f t)`:
This is intended to capture the meaning of "applying a function".
Recall that `f` is required to be a λ-term (that is, NOT restricted to variables only).

It could, for example, be the identity function `(λx.x)`, as in `((λx.x) t)`.
Of course, the result of applying the identity function `t` - is just `t`.

What about `((λx.y) t)`? Well, as we said before, `(λx.y)` always gives you back `y`, no matter what's passed in.
Hence, the result of this application is `y` (whatever *that* is, we simply don't care).


##### Finally, single variables like `x`:
Quite interestingly, this part of the definition - which looks most simple and innocent - may well be the hardest to wrap your head around...

Well, we had assumed "a set `V` of symbols" - but did not say anything about what they would stand for.
In other words: we left them *uninterpreted*. That (exactly) is what makes our calculus "pure".

There are other versions where there's a set of *atoms* which is the union of a set of (uninterpreted) variables as before
**plus** a set of "constants", which are *interpreted* symbols. We might want, for example, have `0` stand for the number zero, `1` for the number one, ... and maybe also `True` stand for truth, `False` for falsehood etc...
Of course we would require that the set of variables (a set of symbols, remember) is *disjoint* from the set of constants (a set of symbols, too), in order to not get confused.
In such a version of the calculus - which is then called an "applied λ calculus" - we would change the definition and allow an *atom* whereever we required a *variable* before.


#### What to do with it?

The short answer is: **everything**!
Well, at least as far as *computation* is concerned. But hey, isn't that already quite a bit? Moreover, there's overwhelming evidence that "this is it" - and all of it.

So here's the thing:

Amazingly, there is principally **no need for** introducing **constants** - in order **to express all of computation**!
And it goes even further: there is a way of getting rid of variables as well! It's called combinatory logic.

In essence, all that's needed to make some "sense" (and in some sense: *all* of sense!) is to have some a-priory notion of
  - a) function
  - b) function application

This, of course, will very soon become tedious in practice and effectively unfeasable - not to speak of efficiency.

However, being able to (principally) break down everything to such simple "bare bones" yields immense power.
A power that has led to the construction of highly complex information processing systems pervading our todays lives, barely noticed as such but more vital than ever in the history of humankind.

[OMG...maybe a little less pathetic?!]

We'll see the "how-to" of all of computation (yes, really!) with nothing but the pure λ calculus next.

#### β-reduction, η-reduction, α-conversion
...





