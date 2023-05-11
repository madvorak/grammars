# Grammars formally in Lean

This commit is synchronized with our [paper](https://arxiv.org/abs/2302.06420) [v2].

## Instructions

In order to install Lean 3, follow the [manual](https://github.com/leanprover-community/leanprover-community.github.io/blob/662aaab1d374a90d85a26e405a1fac698304a281/templates/get_started.md).

In order to download this project, run `leanproject get madvorak/grammars` in your Unix-like command line.

In order to check that the proofs are correct, run `./mk` from the root directory of this project.\
The script will output `Result: SUCCESS` if everything builds successfully.

## Overview

### General grammars

(a.k.a. unrestricted grammars, a.k.a. type-0 grammars, a.k.a. recursively-enumerable grammars, a.k.a. grammars)

[Definition](/src/classes/general/basics/definition.lean)

[Example](/test/demo_general.lean)

[Closure under union](/src/classes/general/closure_properties/union.lean)

[Closure under reversal](/src/classes/general/closure_properties/reverse.lean)

[Closure under concatenation](/src/classes/general/closure_properties/concatenation.lean)

[Closure under Kleene star](/src/classes/general/closure_properties/star.lean)

### Context-free grammars

[Definition](/src/classes/context_free/basics/definition.lean)

[Example](/test/demo_context_free.lean)

[Closure under union](/src/classes/context_free/closure_properties/union.lean)

[Closure under reversal](/src/classes/context_free/closure_properties/reverse.lean)

[Closure under concatenation](/src/classes/context_free/closure_properties/concatenation.lean)

[Non-closure under intersection](/src/classes/context_free/closure_properties/intersection.lean) (\*)

[Non-closure under complement](/src/classes/context_free/closure_properties/complement.lean) (\*)

\* missing proof: [Context-free pumping lemma](/src/classes/context_free/basics/pumping.lean)
