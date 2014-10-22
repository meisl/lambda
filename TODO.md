Unrelated (any order):
- [ ] #8 'put all the missing refs into README'
- [ ] #15 'make a REPL': unclear when exactly it makes sense - but the sooner the better (can always refine it)
- [ ] #16 'add β-/η-reduction and α-conversion to Lamda-Intro.md'
- [ ] #18 'continue docs explaining how to detect & avoid accidental capture during β-red.'
- [ ] #20 'add bibliography'
- [ ] #21 'mention Pierce's TAPL'

To be done in the order given (within each branch):
##### branch 1 (make it self-hosting)
- [ ] #9 'finish ADT List (Church-encoding by hand, everything in λ, too)'
- [ ] #12 'most simple impl of β-red. avoiding accidental capture (in Perl6 only, efficiency is of NO importance)'
- [ ] #10 'add ADT Term for syntax tree / AST entities (Church-encoded by hand)'
- [ ] #11 'implement β/η-red. and α-conv using ADT Term (simple but correct)'
- [ ] #13 'refine β/η-red. and α-conv using ADT Term: clever & efficient & flexible!'
- ...
- [ ] #19 'make a functional parser (like the parser combinators in [Hutt07])'
- ...
- [ ] #23 'make an interpreter using stacked environments' (rather than stupid subst)
- [ ] #24 'implement proper tail calls'
- [ ] #25 'compile to Perl6'

##### branch 2 (make it do *something*)
- [ ] #2 'add most simple symbol-lookup using "δ"'
- [ ] #22 'add comments to syntax'
- [ ] #3 'add hygienic macros using "µ"'
- [ ] #4 'add "if" as a macro'
- [ ] #14 'add "cond" (aka "switch") as a macro'
- [ ] #5 'add "let" as a macro'
- [ ] #6 'add "def"/"define" as a macro, to allow recursive definitions (and maybe local ones)'
- [ ] #7 'add a data-type mechanism, desugaring to a Church-encoding'
- ...
- [ ] #17 'add Types (eventually...)' - oh...
