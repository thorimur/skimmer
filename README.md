# Skimmer

WIP!

This repo provides a hierarchy of features:

1. Declarations tagged with `@[cleanup]` are run at the end of every file.
2. A `LinterWithCleanup` waits for itself to finish running on all declarations, then runs a `cleanup` at the end of each file. In this way, it has the potential to persist state into the environment by modifying refs. (These currently can only be run noninteractively.)
3. `PersistentLinter`s, `AccumulativeLinter`s, and `SimpleAccumulativeLinter`s provide convenient ways to construct a `LinterWithCleanup` with an associated `IO.Ref` and `PersistentEnvExtension` through and into which state can be persisted.

TODO:

4. We provide a `refactor` accumulative linter which can record edits from within linters, and a `write_edits` exe which can write the recorded edits
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
