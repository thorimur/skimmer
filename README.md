# EditTest

WIP!

This repo provides a hierarchy of features:

1. Declarations tagged with `@[cleanup]` are run at the end of every file.
2. `Accumulator`s represent a single connection between a reflike object (such as `IO.Ref`) and a `PersistentEnvExtension`, such that the data in the ref is added to the extension state at the end of each file via a `@[cleanup]`. We also provide ways to construct simple examples of these.
3. `AccumulativeLinter`s are convenient ways to specify a linter which feeds into an `Accumulator`, thus allowing it to persist data.
4. We provide a `refactor` accumulator which can record edits from within linters.
5. We provide an extensible way to provide both syntax- and infotree-based refactoring rules to a `refactoringLinter : AccumulativeLinter`.

### TODO:

1. `@[cleanup]`:
  - figure out correct way to wait for all tasks to finish
    - currently, we can wait for the environment by waiting for checked, but not for linters. We can wait for linters by blocking on a promise in a ref that is resolved only when all syntax ranges have been linted.
  - allow controlling option to be specified in attribute? or simply check during evaluation?
2. `Accumulator`:
  - Make sure `Reflike` makes sense for `Mutex` etc. in `BaseIO`.
3. `AccumulativeLinter`:
  - `SourceIndexed`:
    - get it working! lol
  - for handling interactivity, decide whether we want:
    * two accumulators feeding into the same extension
    * a sum type (or equivalent) in a ref
    * configurability for whether order matters or not, in which case
