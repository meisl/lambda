## An intro to (pure) Lambda calculus:



### λ-terms

Given some (possibly infinite) set `V` of symbols ("variables"),
the set of λ-terms ("Lambda-terms") is defined as:
* every `x` &isin; `V` is a λ-term
* if both, `f` and `t` are λ-terms, then `(f t)` is a λ-term ("Application")
* if `x` &isin; `V` and `t` is a λ-term, then `(λx.t)` is a λ-term ("Abstraction")

Well, that's all about it! ...at least for the syntax :)

---

Note that `f`/`t` or `x`/`t`, respectively, as mentioned in the last two pts, *need NOT be distinct*.

Also note that we just (silently) assumed that none of the special characters `λ`, `.`, `(`, `)` and ` ` (whitespace)
is &isin; `V`, ie. they're not valid symbols (and thus no valid λ-terms either) *in themselves*.

---

OK, so far it's really nothing else but just that: syntax.
But, as you will guess, we can attach meaning to it - in a quite straightforward manner.


### What should λ-terms *mean*? (interpreting them, "semantics")

#### Let's start bottom-up, with Abstraction, `(λx.t)`:
This is intended to denote ***functions***.
Eg `(λx.x)` would be the *identity* function: whatever you pass in - you'll get back the same.
Different is `(λx.y)` which *always* gives you back `y`, no matter what's passed in.

Another one is `(λx.(λy.x))`: this looks a bit more daunting but you can think of it
simply as the two-parameter function which will give you back the *first* argument you gave it
(it really is equivalent to named two-parameter function; please feel encouraged to come back here after the next paragraph on Application and
figure out, step by step, what `(((λx.(λy.x)) u) v)` results in - and you will see).

Similarly, `(λx.(λy.y))` selects the *second* of the two arguments you give it. Again, after
the next paragraph, try to figure out the result of `(((λx.(λy.y)) u) v)`.

**To summarize "Abstraction":**

We use `λ` followed by a variable &isin; `V` followed by a `.` followed by some λ-term called the "body" 
in order to define a function.
What the function does ("returns") is determined by where (and if at all) the variable occurs in the body.


#### Next comes the meaning of Application, `(f t)`:
This is intended to capture the meaning of "***applying a function***", which is simply passing an *argument* to a function (represented by an abstraction, as above) - and retrieving what it returns.
Recall that `f` can be an arbitrary λ-term (that is, it's NOT restricted to just variables).

`f` could, for example, be the identity function `(λx.x)`, as in `((λx.x) t)`.
Of course, the result of applying the identity function to `t` - is just `t`.

What about `((λx.y) t)`? Well, as we said before, `(λx.y)` always gives you back `y`, no matter what's passed in.
Hence, the result of this application is `y`, and `t` is "thrown away" (whatever `y` is we simply don't care).

You know what? Congratulations!

You are now equipped with all the essentials. The rest basically is "mechanics", in the sense that disciplined logical thinking will sooner or later lead you to it, no need for being a genius. Well, for the most part...

Anyways, please try now to evaluate, step by step, the expressions mentioned in the previous paragraph, `(((λx.(λy.x)) u) v)` and `(((λx.(λy.y)) u) v)`.

**To summarize "Application":**

Given an application `(f x)` where `f` is an abstraction (a "λ", for short), we can evaluate/"simplify" it like so:
Let's say the λ's variable is `y` (it may as well be `x` but let's use `y` instead in order to reduce confusion).
Now take the λ's body and replace every occurence of `y` therein with `x`
(ie: with whatever term is `x` - which may well be just `x` itself).
The result of the evaluation/"simplification" is then just the body after that substitution.

If `f` is not an abstraction - well, then so be it. In that case we cannot "simplify" any further and leave things as they are.

---

Note: "simplify" appears in quotes here because there exist cases where the result does not at all look "simpler" after the fact, as we'll see. We'll have to rigorously define what is meant by "simpler". Particularly, it will not, in general, coincide with "shorter".

Also note: the process of substitution as described here is over-simplified. Care must be taken for special cases,
and further conditions must be placed on "every occurence of `y` therein".
All these subtleties don't have any "magic" to them, they're just a bit complicated.
We'll cover them in β-reduction/α-conversion.


#### Finally, the meaning of single variables like `x`:
Quite interestingly, this part of the definition - which looks most simple and innocent - may well be the hardest to wrap your head around...

OK, let's see what we have. We had assumed "a set `V` of symbols" - but did not say anything about what those symbols would stand for.
In other words: we left them *uninterpreted*. That, by the way, is exactly what makes our calculus "pure".

There are other versions where there's a set of so-called *atoms* which is the union of a set of uninterpreted variables (as before)
**plus** a set of "constants", which are *interpreted* symbols. We might want, for example, have `0` stand for the number zero, `1` for the number one, ... and maybe also `True` stand for truth, `False` for falsehood etc...
Of course we would require that the set of variables (a set of symbols, remember) is *disjoint* from the set of constants (a set of symbols, too), in order to not get confused.
In such a version of the calculus - which is then called an "applied λ calculus" - we would change the definition and allow an *atom* whereever we had required a *variable* before.

Anyways - crazy as it may appear at first sight - the very essence of being a "variable" really ***is*** to be left uninterpreted!
Their chief use is as placeholders, most prominently directly after a `λ`, followed by a `.`.
They serve to "get a grip" on something you don't know yet, and that grip you get simply by giving it a name.
For now you should think of a variable as (a name for) something which has an arbitary (= currently unknown) *but fixed* value. That is, the only "variation" there is to a variable is due to *your* (current/local) lack of knowledge, 
and in no way intrinsic to the term "variable" itself.

**To summarize the meaning of "Variables":**

Well, in fact we don't need any meaning for them, as it turns out.
Their whole purpose is to stand for something we don't know (yet) so we can talk about (what to do with) that something we don't know (yet).
Disturbing and viciously circular as all this may appear at the moment,
we'll see how everthing works out well, even with this ultimately reduced "set of tools".


### Now, what can we do with all that (or: "so little")?

The short answer is: **everything**!
Well, at least as far as *computation* is concerned. But hey, that's quite a bit, isn't it?
Moreover, there's overwhelming evidence that "this is it" - and all of it.

So here's the thing:

Amazingly, there is principally **no need for** introducing **constants** - in order **to express all of computation**!
And it goes even further: there is a way of getting rid of variables as well! It's called combinatory logic.

In essence, all that's needed to make some "sense" (and in some sense: *all* of sense!) is to have some a-priory notion of
  - a) function (abstraction, or λ for short)
  - b) function application

This, of course, will very soon become tedious in practice and effectively unfeasable - not to speak of efficiency.

However, being able to (principally) break down everything to such simple "bare bones" yields immense power.
A power that has led to the construction of the highly complex information processing systems pervading our todays lives, barely noticed as such but more vital than ever in the history of humankind.

[OMG...maybe a little less pathetic?!]

We'll talk about the ***how-to of all of computation*** (yes, really!) with nothing but the pure λ calculus next.



### β-reduction, η-reduction, α-conversion
...





