Median cycles: publication checkpoint
====================================

6 October 2026. Prepared with OpenAI Codex (GPT-6 Astra).

Decision
--------

Proceed with a short, explicitly scoped research note. Do not yet submit
to VibeMathed or announce priority. The result treats every centered
symmetric finite unweighted mask on an integer lattice, with an existential
choice of periodic image size. It does not solve Klette's complete
characterization problem for general median operators and finite pictures.

This is a credible smaller publication candidate under the research policy
agreed with the user: complete results are worth recording, while the next
major research allocation should be justified by broader mathematical
consequences. The argument is general in its stated parameters. No further
mask-by-mask enumeration is needed to establish the statement.

What changed in this checkpoint
-------------------------------

The archived antipodal-cut theorem is retained. The old exposing-functional
argument has been replaced by an explicit balanced-base integer map:

  ell(v) = sum_j (2M+1)^j v_j.

It is injective on the coordinate box [-M,M]^d by a leading-digit argument.
Thus the largest absolute projected offset is unique up to sign. The
archived finite flip argument applies directly, with no convex hull,
exposed-vertex theorem or rational-density argument.

The revised proof provides:

* a common coordinate period N <= (2M+1)^d - 1;
* at most floor(p(r-1)/2) improving antipodal flips, with N=2p and r offset
  pairs;
* a compact representation using N signs rather than a full N^d image;
* explicit handling of wrapped sample multiplicities and arbitrarily large
  finite tori with all mask offsets distinct;
* a short, credited proof of the classical finite symmetric-network
  upper bound two on eventual temporal periods.

These are refinements and explicit consequences of the archived proof,
not a claim that the existence theorem was first discovered today. The
period estimate is an upper bound, not a minimal-period theorem. The
construction is not claimed polynomial in the binary input length.

Scope and original source
-------------------------

Klette's 2004 Dagstuhl compilation, Problem 3 (slide 4), asks to characterize
median operators which can generate cycles on finite pictures. The source
does not specify our circular-boundary convention or restrict itself to
centered symmetric masks. Therefore publication must say 'the centered
symmetric periodic case', not 'Problem 3 solved'.

https://tc18.org/openProblems/Dagstuhl_2004.pdf

Directly read the extracted text of the original problem. A screenshot
request failed, so no claim is made to a fresh visual PDF inspection.

Current literature screen
--------------------------

1. Goles, Montealegre, Rios-Wilson and Sene, Dynamical stability of threshold
   networks over undirected signed graphs, arXiv:2309.01854v3.
   Read the total-cycle definitions, Lemma 2, Theorem 1, the counterexample
   remark concerning the stability index, and the discussion. These
   inspected results do not establish the arbitrary-mask periodic lattice
   construction. This is a comparison of the relevant statements, not an
   independent verification of that paper's proofs.

   https://arxiv.org/html/2309.01854v3

2. Jain, Stephan and Tang, Strictly Unfriendly k-Partitions: Sharp Degree
   Thresholds and ETH-Based Lower Bounds, arXiv:2610.04440, posted
   3 October 2026. The abstract concerns complexity on finite graphs.
   The HTML and PDF fetches failed; only the abstract was screened.
   It cannot be ruled out as prior art on that evidence alone.

   https://arxiv.org/abs/2610.04440

3. Conley and Tamuz, Unfriendly colorings of graphs with finite average
   degree, arXiv:1903.05268. The abstract was located, but the full HTML
   fetch failed. A weak unfriendly partition allowing ties does not by
   itself supply the strict inequality needed here. This is a distinction
   between definitions, not a claim to have checked every theorem there.

   https://arxiv.org/abs/1903.05268

4. Kun, Powers and Reyzin, Anti-Coordination Games and Stable Graph
   Colorings, arXiv:1308.3258. Abstract page located; full HTML fetch failed.
   The older archive's fuller assessment is retained as provenance and
   has not been promoted to a fresh full-text verification.

   https://arxiv.org/abs/1308.3258

5. Indexed searches covered symmetric median cycles, strict unfriendly
   lattice/Cayley partitions, total two-cycles, and the exact periodic-mask
   formulation, including site-restricted GitHub, X and VibeMathed queries.
   Many results were irrelevant. No matching universal theorem was found.
   These negative search results provide limited evidence: they do not
   prove novelty or exclude an equivalent result under other terminology.

The August archive also identifies the very-cost-effective bipartition and
offensive-alliance literature. A fresh publisher fetch for the 2015
very-cost-effective paper failed. Its contents were not reverified here.
The appropriate next literature step is targeted access to those full
texts or specialist feedback, not repeated broad keyword searches.
No person has been contacted and no message has been sent.

Verification actually performed
--------------------------------

research-note.tex compiled successfully in the built-in LaTeX editor.
construct.py ran twelve fixed, small examples in dimensions one through
three. It checked 156 projected states, ten improving flips with exact
potential identities, and two direct coordinate-neighborhood median
updates on 408 torus pixels. All checks passed. The direct check sorts
the actual sample values rather than using the cut-count threshold.
The identity mask and the one-pixel torus are explicit controls against
overgeneralization. These are implementation checks, not a proof by search.

No full enumeration, solver search, Lean compilation or Azure deployment
was performed. The input period and sample-work bounds in construct.py
prevent accidental use as a large local search. The general theorem is
supported here by the written mathematical proof.

The inspected August Lean file reaches
exists_antipodal_coloring_meeting_threshold_of_labelled_edges. That endpoint
still assumes the concrete no-internal-edge, incidence and cut-count
identities. The archive records a successful earlier check, but it was not
rerun here. A complete Lean claim would still require the balanced-base
lemma, the actual cyclic edge construction and its identities, and the
lattice pullback with the median definition. No claim of end-to-end Lean
verification is made.

Does this advance the intended research direction?
--------------------------------------------------

Yes for this scoped publication: the complete proof is simpler, quantitative,
constructive and easier to review/formalize. It covers all masks in the
declared class rather than an increasing list of examples.

Not yet as a major new research program: asymmetric masks and boundary
conventions remain outside the argument, and no general reduction to the
full Klette question has been proved. Do not infer a large significance
score merely from the 2004 date. A finite focused review/formalization is
reasonable; an open-ended campaign is not justified by this checkpoint.

The practical deliverable is a mask-dependent oscillating regression input
for synchronous periodic median filters and a precise reason that stopping
only at a fixed point can fail. It is not a claim of improved image quality
or a guarantee about typical real-world images.

Formalization update — 6 October 2026
------------------------------------

The later GitHub preparation closed the previous formalization gap with
a new end-to-end existence proof: Projection, Antipodal, Cyclic, Lattice,
and Result. The Azure development check accepted
MedianCycles.periodic_median_two_cycle, with only propext, Classical.choice,
and Quot.sound. The earlier checkpoint above remains a dated record of
what had been checked at that time. Quantitative period and flip bounds
remain written results outside the current Lean endpoint.
