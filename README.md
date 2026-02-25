# Skimmer

> [!WARNING]
> This repo is very early in its development, and currently only intended for experimental use.

<div align="center">
<a title="A black skimmer (Rynchops niger) in flight, skimming. Pantanal, Brazil. Charles J. Sharp, CC BY-SA 4.0 &lt;https://creativecommons.org/licenses/by-sa/4.0&gt;, via Wikimedia Commons" href="https://en.wikipedia.org/wiki/Rynchops"><img width="512" alt="A black skimmer in flight, skimming, in Pantanal, Brazil" src=".assets/skimmer.jpg"></a>

A black skimmer in flight, doing what this repo does.
</div>

This repo provides ways to *skim* the "surface" of the Lean process—linter executions and file endings—to capture and persist data which is usually ephemeral.

Specifically, we provide a hierarchy of features:

1. Declarations tagged with `@[cleanup]` are run at the end of every file.
2. A `LinterWithCleanup` waits for itself to finish running on all declarations, then runs a `cleanup` at the end of each file. In this way, it has the potential to persist state into the environment by modifying refs. (These currently can only be run noninteractively.)
3. `PersistentLinter`s, `AccumulativeLinter`s, and `SimpleAccumulativeLinter`s provide convenient ways to construct a `LinterWithCleanup` with an associated `IO.Ref` and `PersistentEnvExtension` through and into which state can be persisted.
4. (In progress) We provide a `refactor` accumulative linter which can record edits from within linters, and a `write_edits` exe which can write the recorded edits.
5. (TODO) We provide an extensible way to provide both syntax- and infotree-based refactoring rules to a `refactoringLinter : AccumulativeLinter`.

### TODO:

1. `@[cleanup]`:
  - Consider using a ref instead of an attribute
  - Handle `erased` and scoping; use a more appropriate attribute implementation
2. `AccumulativeLinter`:
  - Handle `#guard_msgs`, which breaks range recording. How do we find the "full" range?
  - Explore handling interactive use
    - Explore not recording ranges at all when interactive
  - Explore writing to other files, not the (main) olean, to make executing the edits better. Reasonable when, as with `Edit`s, we do not rely on the environment etc. to (de)serialize.
    - Explore "fragmentary" module data/other "mostly" environment-independent means of (de)serializing Lean data (e.g. in a "constant" environment/no initializing)
    - Explore using facets?
  - Make setting up controlling options more convenient
  - Explore ways for other linters to hook into framework, esp. tactic analysis framework
3. Infrastructure
  - Create utilities for more targeted actions (e.g. folders instead of library, only dependents of a single file, etc.)
4. Documentation, documentation, documentation!
