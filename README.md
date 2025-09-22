# Skimmer

WIP!

This repo provides a hierarchy of features:

1. Declarations tagged with `@[cleanup]` are run at the end of every file.
2. `Accumulator`s represent a single connection between a reflike object (such as `IO.Ref` or `Std.Mutex`) and a `PersistentEnvExtension`, such that the data in the ref is added to the extension state at the end of each file via a `@[cleanup]`. We also provide ways to construct simple examples of these.
3. `AccumulativeLinter`s are convenient ways to specify a linter which feeds into an `Accumulator`, thus allowing it to persist data.
4. We provide a `refactor` accumulator which can record edits from within linters.
5. We provide an extensible way to provide both syntax- and infotree-based refactoring rules to a `refactoringLinter : AccumulativeLinter`.

### TODO:

1. `@[cleanup]`:
  - figure out correct way to wait for all tasks to finish
    - currently, we can wait for the environment by waiting for checked, but not for linters. We can wait for linters by blocking on a promise in a ref that is resolved only when all syntax ranges have been linted.
  - allow controlling option to be specified in attribute? or simply check during evaluation?
2. `AccumulativeLinter`:
  - Currently each linter has its own cleanup; explore having a single cleanup
  - Explore writing to other files, not the (main) olean, to make executing the edits better. Reasonable when, as with `Edit`s, we do not rely on the environment etc. to (de)serialize.
    - Explore using facets?
  - What happens when other infrastructure ought to hook into accumulators? If they hook directly into the env extension, during elaboration, that's fine. But if a separate linter does this, it becomes more difficult.
  - for handling interactivity (if at all?), decide whether we want:
    * two accumulators feeding into the same extension
    * a sum type (or equivalent) in a ref
    * configurability for whether order matters or not, in which case
3. Infrastructure
  - Handle more targeted actions (e.g. folders instead of library, only dependents of a single file, etc.)
