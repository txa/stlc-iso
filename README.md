# Isomorphisms of simple types are hereditary permutations

Agda formalisation accompanying the paper

> Thorsten Altenkirch. *Hereditary permutations for simple types revisited:
> a baby case for University Algebra.* (arXiv link to follow)

For the simply typed λ-calculus with function types only, it proves:

- **Characterisation**: every invertible β-normal η-long term is a hereditary
  permutation (`STLC.Char.characterisation`, and in the inductive form of
  `STLC.Iso`: `STLC.Link.characterisation-HP`).
- **Easy direction**: hereditary permutations are invertible (`STLC.Easy`), and
  the meaning of every derivation built from `swap : A → B → C ≅ B → A → C`
  and congruence is an isomorphism (`STLC.Sound.derivations-sound`).
- **Coherence**: two derivations are equal modulo the level-2 equations
  (groupoid laws, functoriality, swap², naturality of swap, braid) if and only
  if they have the same meaning (`STLC.Determined.coherence`), every
  derivation is equal to a canonical one (`STLC.Coherence.normal`), and every
  isomorphism is the meaning of a derivation (`STLC.Derivable.surjective`,
  via `STLC.Derivable.hp-derivable`: the canonical derivation of a hereditary
  permutation has that permutation as its meaning).

The proof of the characterisation is purely syntactic: a descent through both
components of an isomorphism at once, with no completeness theorem.

## Checking

Agda 2.6.5, no libraries (only Agda's builtin modules):

```
agda Everything.agda
```

There are no postulates, holes or termination pragmas. The development uses
`--rewriting` for three equations on context concatenation (and
`--local-confluence-check` where they are declared), and the K rule (Agda's
default).

## Modules

| module | content |
|---|---|
| `Prelude` | equality, Σ, lists, `All` |
| `Syntax` | types, intrinsically typed spine normal forms, weakening, η-expansion, hereditary substitution |
| `Lemmas` | substitution lemmas; normal forms form a category |
| `Subst` | simultaneous substitution, its category laws, pairing |
| `Iso` | isomorphisms, derivations and their meaning, hereditary permutations, statements |
| `Heads` | occurrences, free and bound heads; no creation; heads under substitution |
| `LamI` | the λI predicate and its preservation |
| `Tele` | telescopes, bodies of η-long terms, spines as substitutions |
| `Descent` | matched pairs and the descent; relevance |
| `Thin` | thinnings, strengthening, cancellation of renamings |
| `Char` | no stray variables; the characterisation |
| `Easy` | hereditary permutations are invertible |
| `Link` | from the predicate form of hereditary permutations to the inductive family |
| `Coherence` | level-2 equations, insertion form, normal forms of derivations |
| `Sound` | soundness of the level-2 equations |
| `Determined` | canonical derivations are determined by their meaning; coherence |
| `Derivable` | the meaning of a canonical derivation is its hereditary permutation; surjectivity |
| `Examples` | checks by computation |

## Use of AI tools

This development and the accompanying paper were produced in collaboration
with Claude (Anthropic), used through Claude Code: Claude drafted Agda code and
text, ran experiments and searched the literature, under the author's
direction. The author has checked the content and is responsible for it.
