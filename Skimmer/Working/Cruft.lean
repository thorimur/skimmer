module

import Lean.Elab.Command




/-
It's going to have the following flow

----
We're in a library/package. We're fed the **target** we want to refactor. Let's say for convenience it's a **single module**.

**mod**
 ↓
filepath -- could start here for convenience
 ↓ read
string

----
Then we need to get the header, and the imports, and everything needed for the environment. Ideally we also allow operating on the header here to create intermediate data.

string
 ↓ parse
header syntax + parser state
 ↓ "elab"
`Import`s (module names + modifiers)

----
We also need the previous data.

`Import`s
 ↓
filepaths
 ↓
skimmer build artifact filepaths
 ↓
deserialize β
↘↓↙ merge
initial β state


----
Now we need to construct the environment in the orchestrator.
In the future this will be a subprocess...somehow.
For now we're hardcoding the folded state + functionality. In the future these will be general.

`Import`s
 ↓ importModules
env   ↙ Command.State? ↙ Syntax? Parser state? -- Where exactly do we parse + get the next cmd?
→↓ IO.processCommand or Language.Lean.processCommand or some other internal?
 ↓ ???
Array of `InfoTrees`, `Syntax` ???  ↙β
 ↓ tool
β + edits + next command state
↑←
...
{terminal command encountered}
 ↓
store β + edits in skimmer build artifact...writeModule? can we deserialize without init?

  [future] Possible interactivity + pickup point/suspended process instead of re-running.

----
Now we need to read the edits to display to the user.

filepath
 ↓
skimmer build artifact
 ↓ deserialize
displayed edits + button for writing them

---
To write the edits:

  [future] new git worktree, incorporate into loop with reparsing + re-elab

filepath
 ↓
skimmer build artifact
 ↓
deserialized edits
 ↓ write to source
(altered source file)


-- Idea/aside: representing no-op effects with wrapper types for Lake. They don't maintain reference to the actual jobs, but they tell us something like that there *will* be a file here, or something?


----
At the beginning:

dive file with syntax specifying module
 ↓
module
 ↓
...

-/
/-
# Environment fluency

- In the future we want to be have a metaprogramming API for *internal data capture*, i.e. by allowing a source-level metaprogram to catch data itself (a la the to_additive refactor). It can put stuff in the environment, then we read it.
- We can pass along data externally. The difficulty maybe is allowing this state to be extensible. We don't have any other environment to add it to, so for extensibility we **will** probably need to **add our things to the source environment**. This can be done during `importModules` or manually. Manual might make sense for attribute-only stuff? Not sure. (Ensure no conflict with source-imported versions of the same)
  - An alternative for extensibility is recompiling the executable with our refactors and such inlined.
  - Another alternative is using plugins, but carefully! E.g. dynlibs and such. Requires building shared facets and such for our tools though. Not too much of an issue if they're all in a library it sets up for you.
  - For now let's hardcode a single function


-/
