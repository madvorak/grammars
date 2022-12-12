# Grammars formally in Lean

Below you find what has been completed so far.

## Context-free grammars

[Definition](https://github.com/madvorak/grammars/blob/main/src/context_free/cfg.lean)

[Example](https://github.com/madvorak/grammars/blob/main/test/cfg_demo.lean)

[Closure under union](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_union_CF.lean)

[Closure under concatenation](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_concatenation_CF.lean)

[Closure under reversal](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/reverse_CF.lean)

[Non-closure under intersection](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_intersection_CF.lean) (*)

[Non-closure under complement](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/complement_CF.lean) (*)

* missing proof: [Context-free pumping lemma](https://github.com/madvorak/grammars/blob/main/src/context_free/cfgPumping.lean)

## Context-sensitive grammars

[Example](https://github.com/madvorak/grammars/blob/main/test/csg_demo.lean)

## Unrestricted grammars

(a.k.a. general grammars, a.k.a. recursively-enumerable grammars, a.k.a. type-0 grammars, a.k.a. grammars)

[Definition](https://github.com/madvorak/grammars/blob/main/src/unrestricted/grammar.lean)

[Example](https://github.com/madvorak/grammars/blob/main/test/grammar_demo.lean)

[Closure under union](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/binary/RE_union_RE.lean)

[Closure under concatenation](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/binary/RE_concatenation_RE.lean)

[Closure under Kleene star](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/unary/star_RE.lean) (was the most difficult proof; see [informal description](https://github.com/madvorak/grammars/blob/main/informal/KleeneStar.pdf) for the big picture)

[Closure under reversal](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/unary/reverse_RE.lean)
