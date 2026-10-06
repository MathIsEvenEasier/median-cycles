Periodic two-cycles for symmetric median masks
=============================================

Every nontrivial centered symmetric finite mask on an integer lattice
admits a periodic binary image which changes every pixel at each
synchronous median update. Applying the filter twice recovers the image.

This repository records the centered symmetric periodic case of the
median-cycle question. It does not characterize asymmetric masks, settle
Klette's full Problem 3, or guarantee a cycle on every prescribed image
size. Literature priority remains unconfirmed.

The statement
-------------

Choose a nonempty finite family of nonzero offsets a_i in Z^d, with no two
equal up to sign. The mask contains the center and each pair +a_i, -a_i.
Encode binary pixels by signs -1 and +1. The median is the sign of the sum
of these 2r+1 samples. Updates are synchronous.

There exist a positive common coordinate period N and a binary image x
such that F(x) is its pointwise complement. Consequently F(F(x))=x and
F(x) differs from x at every pixel. Wrapped samples retain their
multiplicity when offsets coincide on the finite torus.

If every coordinate has absolute value at most M, the period satisfies
``2 <= N <= (2M+1)^d - 1``. Write N=2p and let r be the number of offset
pairs. Any sequence of improving antipodal flips has at most
``floor(p*(r-1)/2)`` steps. Both bounds are included in Lean. The spatial
bound is an upper bound, not a claim that the period is minimal.

Proof
-----

* A balanced-base linear encoding separates all offsets and their negatives.
  The largest absolute projected offset p is unique up to sign.
* Work on the cyclic group of order 2p. Restrict to colorings that reverse
  their sign under translation by p.
* Minimize the integer interaction energy of the remaining offsets over
  this finite nonempty set of colorings. Flipping an antipodal pair gives
  the local inequality needed at every pixel.
* The two extreme samples both have the opposite sign. Together with the
  remaining-neighbor inequality they force a strict majority against the
  center. Pull back through the linear encoding to obtain a periodic
  lattice image.

Lean sources
------------

`Projection.lean <formal/Projection.lean>`_ proves balanced-base injectivity.
`Antipodal.lean <formal/Antipodal.lean>`_ proves the exact energy change and existence of a minimum.
`Cyclic.lean <formal/Cyclic.lean>`_ constructs the antipodal state and applies the actual median.
`Lattice.lean <formal/Lattice.lean>`_ selects the extreme offset and proves the periodic pullback.
`Result.lean <formal/Result.lean>`_ states the genuine two-cycle, including its spatial-period bound.
`FlipBound.lean <formal/FlipBound.lean>`_ proves the energy range, the exact drop of an improving
flip, and the bound for any actual sequence of such flips. Its ``S.card``
is the number r-1 of remaining offset pairs.

The full existence theorem and both quantitative bounds passed Lean
checking in bounded Azure sessions on 6 October 2026. Their dependencies
are exactly the standard ``propext``, ``Classical.choice``, and ``Quot.sound``.
There are no project postulates, proof holes, native decision shortcuts,
or unsafe declarations.

The public source build succeeded on 6 October 2026:
`Lean verification run <https://github.com/MathIsEvenEasier/median-cycles/actions/runs/37496221585>`_.
It checked commit ``96a4c670aae9285c8e78a290cd3897aece83a1e0``: seven
positive modules compiled, ten named declarations passed the axiom audit,
and the intentionally invalid proof was rejected as expected.

`Permanent verification records <evidence/public-ci-2026-10-06/>`_ include
the full theorem statements, compiler logs, source hashes, and provenance.
The checked Lean sources are identified by ``evidence/source-manifest.json``;
later documentation and evidence commits do not change those files.

The primary endpoints are ``MedianCycles.periodic_median_two_cycle_bounded``
and ``MedianCycles.cyclic_improving_flip_bound``. The build prints both
complete statements and their axiom dependencies.

Reproducibility
---------------

Lean 4.34.0; mathlib commit
``5ed2965256430c3649e86755f9576b54eca72435``.
The public workflow rebuilds every project module from source on an
Azure runner. Mathlib's pinned dependency cache is downloaded; no compiled
project proof is accepted as input. The build prints the final theorem
and its axiom dependencies, and checks that an intentionally invalid
proof is rejected.

All compilation runs on a disposable Azure VM with a 24 GiB cgroup memory
limit, no swap, a 115-minute worker limit, and an independent cloud deletion
guard. The controller also collects results and verifies resource deletion.
`Cleanup receipts <evidence/azure-cleanup-2026-10-06.json>`_ confirm that
all compute and control resources of the four verification sessions were
deleted. Workflow dispatch requires the unique label of a provisioned runner.
Scripts intentionally refuse a local full build.

Practical use
-------------

The construction gives an oscillating regression input for every allowed
synchronous periodic median filter. A loop which stops only when two
consecutive images are identical can fail to terminate. This is a
worst-case termination result, not a claim about typical image quality.

``scripts/construct.py`` supplies a bounded reference constructor and
checks its output by sorting actual neighborhoods. Its small fixed tests
are implementation checks, not the proof of the general theorem.

Provenance and references
-------------------------

The antipodal-cut construction comes from the supplied research archive
of 21 August 2026. The October revision gives an elementary projection
argument, quantitative bounds, and an end-to-end formalization project.
Prepared with OpenAI Codex (GPT-6 Astra).

* R. Klette (compiler), Open Problems in (Digital) Geometry, Dagstuhl,
  March 2004, Problem 3, slide 4:
  https://tc18.org/openProblems/Dagstuhl_2004.pdf
* E. Goles, P. Montealegre, M. Rios-Wilson and S. Sene, Dynamical stability
  of threshold networks over undirected signed graphs, arXiv:2309.01854v3:
  https://arxiv.org/html/2309.01854v3

The classical period-at-most-two result for symmetric threshold dynamics
is background. Our existence claim for all masks in the stated class is
not accompanied by a claim of priority or independent expert review.
