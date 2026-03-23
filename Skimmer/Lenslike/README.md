# Scrappy Lenses

A "lens" abstracts the notion of trying to update some underlying data given information on how a "view" of that data should update. Unfortunately, this (and most variants) is too rigid for us. We need to be able to get the job done even when we don't have proofs of well-behavedness, even when we don't want to update the view per se, even when we don't know what we want but have to go find it anyway...we need to be *scrappy*.

Let's outline our situation a bit.

We have some source code, some context in which it gets elaborated, some elaboration artifacts produced along the way. From this, at *multiple points*, we want to figure out (in a refactor) how we can modify the source to produce an elaboration result that satisfies some predicate...all within the context created by *other* refactors.

So, each refactor (let's stick with this example, since it's fairly rich) should take in a
- *old input context and artifacts* (for reference)
- *new input context* (produced by refactors it's sensitive to)...or, importantly, some *sufficient data* recorded by previous refactors which characterizes the delta from the old context to the new context
- *locus* state: each refactor has a locus of action, whether it's a kind of need it may communicate (e.g. "hey, I need this option set here, tell the outer refactorer to set it at the command level") or a region of syntax it's allowed to alter

and gives us
- *new output context* seen by future refactors (or the corresponding sufficient delta)
- *response*, which may e.g. say how to modify the locus, communicate failure and pause the iteration, communicate alternatives, explain "reasoning" behind the choice, provide metadata on the choice, etc.
  - In this response we include the effect on the locus.

Moreover, these refactors occur within an iteration through emulated steps of elaboration. It's not clear that we always want to hew to the actual chronological order; sometimes we might want to do things in parallel if we know dependencies do not obtain between effects of various refactors, sometimes we might want to work backwards... There is also an implicit step of detection, wherein we test the (old/new) context and artifacts to see if we need to compute a refactor.

Note that there are some shortcuts we can take sometimes. For example, what if we didn't actually feed the input context along? Instead, what if the new input context is computable from anticipating success of earlier refactors and their effect on the old input context?

Likewise, where does the locus come from? This is something we compute, and presumably *encode changes to*.

But the difficult part is really:

> If the locus produced this artifact in this previous context, how does it need to change to produce an artifact satisfying some success predicate `p` in the new context?"

(Note: We ultimately want a richer measure than "success/failure", to allow needs-review successes, best-effort failures, and other sorts of communication/policies)

In some sense, we would benefit from being able to compute a *derivative* of the functions involved. But that sort of automatic, generalized-to-DTT differentiation is hard, rigid, and potentially costly. Instead, is there a way to *declare* the derivative in some fashion? To say that these sorts of changes depend also on these other changes from the old context to new, and have such-and-such sorts of effects on our success predicate or inputs to our success predicate?