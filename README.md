# Forematics is a Metamath verifier written in Nim

![Github Actions](https://github.com/treeform/forematics/workflows/Github%20Actions/badge.svg)

## Usage

```
forematics mm/set.mm
```
## Metamath

[Metamath](http://us.metamath.org/) is project that attempts to describe mathematics from ground up starting from very simple axioms, following very simple rules, building more and more complex theorems on top, while having everything machine checked using a very simple verifier. It has one of the largest collection of over 30,000 theorems and their proofs. [Forematics](https://github.com/treeform/forematics) is a [Metamath](http://us.metamath.org/) verifier written in Nim.

Metamath is a pure math language that looks like this:

```
⊢ ((𝐴 ∈ ℝ ∧ 𝐴 ≠ 0) → ∃𝑥 ∈ ℝ (𝐴 · 𝑥) = 1)
```
*Example of an Axiom: [Existence of reciprocal of nonzero real number](http://us.metamath.org/mpeuni/ax-rrecex.html).*

## Forematics

Forematics is build like any simple interpreter with with a tokenizer, parser and an eval loop. It has ability to define constants, variables, axioms and theorems (kind of like functions). It then uses a simple interpreter to verify that all theorems based on starting axioms are valid.

All "evaluation" is done by the substitution rule. There is no other built in concepts. Using the substitution rule it derives all concepts like what numbers are. Including how parentheses `()`, if-then, `+`, `-`, and all other math operators. It only [proves](http://us.metamath.org/mpegif/1p1e2.html) `1 + 1 = 2` after defining 11086 other theorems and it [proves Pythagorean theorem](http://us.metamath.org/mpegif/pythag.html) `z² = x² + y²` after defining complex numbers after doing 24464 other theorems.

Forematics can't be used compute, derive or solve equations, it's not a [Computer algebra system](https://en.wikipedia.org/wiki/Computer_algebra_system) but maybe a small part of one that only deals with proofs... and very simple and constrained proofs at that.

Forematics is fast, because Nim is fast, and can verify and prove 30,000 proofs in 21 seconds.

## mmverify.py

Big thanks to the https://github.com/david-a-wheeler/mmverify.py project which was used a base and insperation.

## sets.mm

Download the latest set.mm from https://github.com/metamath/set.mm
