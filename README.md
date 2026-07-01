# Memoized Derivatives for Fast Filtering and Schema Validation of Semi-Structured Data (Lean)

Proofs written in [Lean4](https://leanprover.github.io/) of [Katydid](http://katydid.org.za/)'s memoization technique for the paper: Memoized Derivatives for Fast Filtering and Schema Validation of Semi-Structured Data.

![Check Proofs](https://github.com/katydid/paper-2026-mem-filter-lean/workflows/Check%20Proofs/badge.svg)

Here we formalize the core of the [Katydid](http://katydid.org.za/) filtering algorithm.
This algorithm allows us to filtering through millions of serialized data structures per second on a single core.
We recommend following the [Readme](./VerifiedFilter/Readme.md) documents, to get an overview of each folder.

## Setup

  - [Install Lean4](https://lean-lang.org/install/).
  - Remember to also add `lake` (the build system for lean) to your `PATH`.  You can do this on mac by adding `export PATH=~/.elan/bin/:${PATH}` to your  `~/.zshrc` file
