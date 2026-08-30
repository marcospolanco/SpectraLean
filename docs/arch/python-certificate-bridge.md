# Proposal: A Python Certificate Bridge for Scaffold's Spectral Certificates

**Status:** Proposed 2026-08-30. **Gated — human decision required**
(see §Gate). Not an autonomous-agent milestone: this is an
ecosystem/adoption initiative outside the center-out SGT-proof
priority order (`AGENTS.md` § Priority order), not a theorem to prove.
No Lean, Python, or documentation change is authorized by this
document alone.

## Provenance

This proposal writes up a chat discussion (2026-08-30) that converged
on a specific, scoped idea after rejecting two broader ones. Recorded
here so the reasoning survives, not just the conclusion.

## The question this answers

Scaffold's actual mathematical territory (Laplacians, Cheeger bounds,
spectral partitioning, sparsification, concentration inequalities) is
already covered *numerically* by an active Python ecosystem —
NetworkX, PyGSP, NetworKit, SciPy's sparse eigensolvers, and (outside
Python) Julia's `Laplacians.jl`. Every one of those computes a
floating-point answer whose correctness rests on "the algorithm is
textbook-known-correct, assuming the implementation matches the
textbook" — no machine-checked guarantee that a specific returned
number actually satisfies the claimed bound. The question: is there a
tractable way for Scaffold's proofs to serve that existing ecosystem,
rather than compete with it or sit unused beside it?

## Two rejected framings, and why

1. **"Certify these implementations."** Proving that PyGSP's actual
   Lanczos code, or NetworkX's power-iteration PageRank, computes what
   it claims *in general* requires floating-point rounding-error
   analysis — bounding how IEEE-754 arithmetic accumulates error across
   an algorithm's iterations. This is a real, different mathematical
   discipline from anything in Scaffold today (everything here is exact
   rational/real arithmetic with zero floating-point error modeling),
   and it would mean formalizing claims about a specific external
   library's source code staying stable — a maintenance liability, not
   a proof. Rejected as the framing, not as impossible; it's simply a
   different, much larger project than this one.
2. **"Wrap the popular packages' own API."** Considered and rejected
   for a different reason: forcing a new calling convention or graph
   representation on top of what NetworkX/PyGSP users already have is
   pure adoption friction for a tool whose entire value is trust, not
   convenience. Nobody adopts a correctness tool that also asks them to
   rewrite their code.

## The scoped idea

**Per-output certification, not implementation verification.** A thin
Python bridge that takes a numerical claim someone already has — a
graph they already built (a NetworkX graph, a PyGSP `Graph`, a plain
`scipy.sparse` matrix) and a number they already computed
(`nx.algebraic_connectivity(G)`'s return value, or a candidate Fiedler
vector) — and answers, via a **kernel-checked Lean computation**,
whether that specific claim actually satisfies a proved bound. It
never inspects or trusts how the number was computed; it only checks
whether the number is true.

This already has almost all of its mathematical foundation built:
`Scaffold/Mathlib/GraphTheory/SpectralCertificates.lean` defines
`isSpectralUpperBoundCertificate : Matrix V V ℚ → (V → ℚ) → ℚ → Bool`
— a plain computable check (orthogonality to `onesVec`, positive norm,
the cross-multiplied Rayleigh-quotient inequality) — with the soundness
theorem `lambda2_le_of_certificate`: if the Bool-valued check returns
`true` on a symmetric nonnegative rational network, the network's
*real* algebraic connectivity `lambda2` genuinely satisfies the claimed
bound. There is also a **kernel-verifiable integer twin**
(`isSpectralUpperBoundCertificateInt`/`IntFrac`), stated so that
`decide` can evaluate it directly inside the Lean kernel on a concrete
`Fin n` graph — already exercised end-to-end this way in
`Scaffold/QA/SpectralGraph/SpectralCertificates_QA.lean`. The proof
work this proposal would need is close to zero; the work is entirely
the bridge.

## API design: adapters, not a new library

The Python surface a user touches should be the smallest possible
addition to code they already have, in two shapes:

- **A function call**, for one-off checks:
  ```python
  from scaffold_certify import certify_lambda2_upper_bound

  lam2 = nx.algebraic_connectivity(G)          # their existing call, unchanged
  certify_lambda2_upper_bound(G, lam2)          # raises / returns a verdict
  ```
- **A decorator**, for zero-change adoption at a call site someone
  already has in a codebase:
  ```python
  @scaffold_certified
  def compute_connectivity(G):
      return nx.algebraic_connectivity(G)
  ```
  The wrapped function's return value passes through unchanged on
  success; on failure it raises with the Lean-checked counter-evidence,
  not a vague warning.

Both accept native objects from the libraries people already use
(`networkx.Graph`, `pygsp.graphs.Graph`, `scipy.sparse` matrices, or a
plain adjacency array) via small format adapters — never a new graph
representation Scaffold invents and asks the ecosystem to adopt. The
third-party packages themselves are never modified, forked, or
vendored; the bridge only ever sees their output.

## The non-negotiable trust-preserving constraint

The check must invoke the **actual Lean-checked decision procedure**,
not a Python reimplementation of the same rational arithmetic. This is
the whole point of the exercise: a hand-written Python "equivalent" of
`isSpectralUpperBoundCertificateIntFrac` could silently drift from what
`lambda2_le_of_certificate` actually proves, quietly reopening the
exact trust gap this bridge exists to close. Concretely, the bridge
should:

1. Convert the user's rational-rounded test vector and bound into
   Lean literals for the concrete vertex type (`Fin n`).
2. Generate a small Lean source file instantiating the **integer**
   certificate checker (`isSpectralUpperBoundCertificateIntFrac`) at
   those literals, ending in a `#eval` or `decide`-backed assertion.
3. Invoke Lean itself (`lake env lean` on the pinned toolchain, or a
   longer-lived Lean server process for latency — an open Step 0
   question, see below) to kernel-check that file.
4. Report the verdict, and on success, cite `lambda2_le_of_certificate`
   by name as the theorem that makes the verdict meaningful — the
   Python layer should never claim more than the Lean theorem actually
   proves.

## The honest open problem: floating point to exact rational

A certificate is stated over ℚ (or ℤ); a NetworkX/PyGSP output is an
IEEE-754 float. Rounding the float to a "nearby" rational is not free
of judgment calls this proposal does not resolve in advance:

- Round too coarsely and the certificate may fail to hold even though
  the true value is close (the check is exact, not approximate — a
  bound of `2.0000001` will not certify against a claimed `2`).
- Round too finely (e.g., the float's full 53-bit mantissa as an exact
  rational) and the resulting integers may make the kernel `decide`
  call slow, since the integer twin's cost scales with the literals'
  size, not just the graph's.
- The "bounded error rate" framing from the originating discussion
  means the certificate should probably target *"is the true value
  within `ε` of the claimed one"* rather than exact equality — which
  needs a paired upper- and lower-bound certificate (the existing
  machinery gives the upper-bound direction; a symmetric lower-bound
  certificate would need its own small Lean lemma, likely cheap given
  `lambda2_le_of_certificate`'s own proof route, but not yet written).

This is real Step 0 material for whoever picks this up, not a detail
to wave at.

## Acceptance bar (for a future Step 0, not authorized here)

- The bridge changes zero lines in any third-party package.
- A round-trip demonstration: take a NetworkX graph, compute
  `algebraic_connectivity` normally, certify it, and separately
  demonstrate the bridge correctly *rejects* a deliberately wrong
  claimed bound (a negative-control test, per this project's own
  QA discipline).
- The certificate verdict is traceable to the actual Lean theorem name
  and file — never a bare "verified" with no citation.
- Latency is measured and reported honestly; if per-call Lean
  invocation is too slow for interactive use, that is a valid Step 0
  finding (a persistent Lean server, or a documented batch-only mode)
  rather than a reason to weaken the trust constraint above.

## Non-goals

- **Not implementation verification.** This does not prove PyGSP's or
  NetworkX's algorithms correct in general, and should never be
  described that way — see the first rejected framing above.
- **Not floating-point error analysis.** No claim is made about IEEE-754
  rounding behavior; the bridge certifies a rational value someone
  chooses to check, honestly rounded, nothing about the float that
  produced it.
- **Not a new graph library.** No new graph data structure, no new
  numerical algorithms — Scaffold does not compute anything here, only
  checks.
- **Not limited to `lambda2`.** The λ₂-upper-bound certificate is the
  only one that exists today; a real Step 0 would need to inventory
  which other Scaffold theorems (Cheeger, expander mixing, the
  degree-eigenvalue sandwich) admit the same decidable-certificate
  treatment before promising broader coverage.

## Gate

Blocked on an operator decision, for the same reason
`clean-room-sgt-export.md` and similar documents are gated: this is an
adoption/ecosystem investment, not a mathematical milestone the
center-out policy would rank on its own terms. It also creates a new
kind of artifact (a Python package with its own release, packaging,
and support surface) that this project has never maintained before —
a real, ongoing commitment beyond a one-time Lean delivery. An
autonomous run should not begin Step 0 on this without an explicit
go-ahead.
