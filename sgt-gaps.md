# Remaining Scaffold dependency for the spectral-proof rewrite

## Graph heat semigroup — pending

The clean-sheet `spectral-proof` rewrite needs one remaining piece of
standard mathematics from `../scaffold`: Phase B of
[`reversibility-and-heat-semigroup.md`](proposals/reversibility-and-heat-semigroup.md).

Scaffold must provide a graph-level finite heat-flow interface for a
symmetric weighted Laplacian:

- heat evolution specialized to `laplacian A`;
- identity at time zero and the semigroup law;
- preservation of `onesVec` (mass conservation);
- eigenmode decay, including the connected-graph consequence that free
  diffusion leaves only the DC component in the limit.

**Gate:** Scaffold's operator decision for Phase B is still pending. The
rewrite is the named consumer once that decision is recorded.
