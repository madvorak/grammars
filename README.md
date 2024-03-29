# Grammars formally in Lean

## Instructions

In order to install Lean 3, follow the [manual](https://leanprover-community.github.io/get_started.html).

In order to download this project, run `leanproject get madvorak/grammars` in your Unix-like command line.

In order to check that the proofs are correct, run `./mk` from the root directory of this project.\
The script will output `Result: SUCCESS` if everything builds successfully.

## Overview

Below you find what has been completed so far.

### Context-free grammars

[Definition](/src/classes/context_free/basics/definition.lean)

[Example](/test/demo_context_free.lean)

[Closure under union](/src/classes/context_free/closure_properties/union.lean)

[Closure under reversal](/src/classes/context_free/closure_properties/reverse.lean)

[Closure under concatenation](/src/classes/context_free/closure_properties/concatenation.lean)

[Non-closure under intersection](/src/classes/context_free/closure_properties/intersection.lean) (\*)

[Non-closure under complement](/src/classes/context_free/closure_properties/complement.lean) (\*)

\* missing proof: [Context-free pumping lemma](/src/classes/context_free/basics/pumping.lean)

### Context-sensitive grammars

[Example](/test/demo_context_sensitive.lean)

### Unrestricted grammars

(a.k.a. general grammars, a.k.a. type-0 grammars, a.k.a. recursively-enumerable grammars, a.k.a. phrase-structure grammars, a.k.a. grammars)

[Definition](/src/classes/unrestricted/basics/definition.lean)

[Example](/test/demo_unrestricted.lean)

[Closure under union](/src/classes/unrestricted/closure_properties/union.lean)

[Closure under reversal](/src/classes/unrestricted/closure_properties/reverse.lean)

[Closure under concatenation](/src/classes/unrestricted/closure_properties/concatenation.lean)

[Closure under Kleene star](/src/classes/unrestricted/closure_properties/star.lean)
