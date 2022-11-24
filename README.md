# Formalization of formal grammars

I formalize formal grammars in Lean. I started with context-free grammars. Hopefully, this project will cover the whole Chomsky hierarchy in the future.

### Context-free grammars

[Definition](https://github.com/madvorak/grammars/blob/main/src/context_free/cfg.lean)

[Example](https://github.com/madvorak/grammars/blob/main/test/cfg_demo.lean)

[Closure under union](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_union_CF.lean)

[Closure under concatenation](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_concatenation_CF.lean)

[Closure under reversal](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/reverse_CF.lean)

[Non-closure under intersection](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_intersection_CF.lean)

[Non-closure under complement](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/complement_CF.lean)

Missing proof: [Context-free pumping lemma](https://github.com/madvorak/grammars/blob/main/src/context_free/cfgPumping.lean)

### Recursively-enumerable grammars

[Definition](https://github.com/madvorak/grammars/blob/main/src/unrestricted/grammar.lean)

[Example](https://github.com/madvorak/grammars/blob/main/test/grammar_demo.lean)

[Closure under union](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/binary/RE_union_RE.lean)

[Closure under concatenation](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/binary/RE_concatenation_RE.lean)

[Closure under reversal](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/unary/reverse_RE.lean)
