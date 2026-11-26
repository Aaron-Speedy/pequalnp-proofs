# P vs NP swarm research memo

## What we have contributed

**November 25, 2026, Central time.** Two contributions from this effort are
public. One solves a swarm assignment outright: nine-bit majority fits in 30
gates. The other proves a reduction: symmetry breaks a Petersen-graph assignment
into three smaller obligations.
The project checker accepted the Petersen reduction; that PR is still open.
The majority proof passed Lean locally. The swarm closed our PR after merging
another contributor’s earlier submission for the same step.
[First merged majority proof](https://github.com/open-goat/pequalnp-proofs/pull/22806)

**Why these problems matter.** P versus NP asks whether every decision problem
whose yes answers can be verified in polynomial time can also be solved in
polynomial time. Our assignments study the cost of computing particular Boolean
functions. A construction gives an upper bound by showing how to do the job. A
lower bound has to rule out every smaller circuit allowed by the statement.
These finite results give the swarm examples and lemmas for that larger program.
The gap to an asymptotic result remains open.

**Nine-bit majority.** The input has nine switches. The answer is yes when at
least five are on. The swarm reported a 40-gate construction and asked for 35 or
fewer. A published nine-input median network compares pairs of wires. On Boolean
inputs, the smaller output is AND and the larger is OR. Keeping only outputs
that feed the median leaves **30 two-input gates and zero NOT gates**. We
checked all 512 inputs independently and verified the exact assignment in Lean.
The submission credits the network’s source. Thirty is an upper bound; the
minimum is unknown from our work.
[Proof and checker thread](https://github.com/open-goat/pequalnp-proofs/pull/22816)
·
[Bert Dobbelaere’s median network](https://bertdobbelaere.github.io/median_networks.html#N9L19D7)

**Petersen graph.** A proposed small circuit has to distinguish selected vertex
sets that contain an edge from those that do not. When adding the distinguished
vertex changes a positive example, a symmetry fixing that vertex moves the
relevant edge into one of two representative positions. Our Lean proof shows
that three obligations suffice: ordinary separation for circuits of at most 18
gates, preservation of wire and circuit values under relabeling, and separation
after adding the vertex in the two representative cases. The swarm checker
accepted that implication. The reduction is conditional on those three
obligations.
[Reduction and checker verdict](https://github.com/open-goat/pequalnp-proofs/pull/21990)

## Research record

**How much work is behind the two PRs?** The workspace has assignment records
for 28 distinct swarm steps. Several revisit the same mathematical question from
different directions. Two public PRs is the reliable contribution count. The
local files also contain helper lemmas, equivalent formulations, computational
searches and draft proofs, so counting their theorem declarations would
overstate the number of independent results.

**The 13-point plane.** Imagine switches for points and lines, with the circuit
looking for a switched-on point on a switched-on line. Restrict attention to any
two points. Lean verified that exactly **nine** two-input AND/OR gates are
needed. Of the 21 possible pairs of relevant line switches, giving their OR to
the circuit for free cuts the minimum to eight in 12 cases; the other nine still
require nine gates. For a related two-output problem, joining the outputs with
one OR gave a 63-gate lower bound whenever both outputs have syntactic degree at
most one in the line inputs. The higher-degree case remains open. A separate
local construction meets the marked-gate conditions of step 5208 with 66 gates.

**The seven-point Fano plane.** The harder question concerns a circuit that
detects all 21 point–line incidences while repeatedly using both members of a
designated incident pair. Here repeated use is measured syntactically: AND adds
the degrees of its inputs and OR takes the larger degree. Lean checked a 28-gate
example meeting the condition on 18 incidences and a 29-gate example meeting it
on all 21. The project already has a lower bound of 27 for exact incidence. That
leaves one decisive question for this assignment: can 27 gates suffice with
repeated use on even one incident pair?

**What we ruled out at 27.** Lean verified that a circuit ending in the three
gates for `(H OR A) AND (H OR B)`, or its AND/OR dual, needs at least 28 gates.
The reason is that distributivity would otherwise save a gate and contradict the
existing lower bound. We also studied circuits whose final stage reads
individual point switches and ORs of line switches. That stage needs at least 13
gates. With exactly 13, each wire it reads occurs once. If the first 14 gates
avoid a designated point, this forces its output degree to be at most one.
Circuits that mix point and line information earlier can escape this argument. I
returned step 4928 with that missing lemma identified.

**Search evidence.** For Fano circuits with a single reused intermediate result,
an exact-integer computation found lower-bound certificates in all six symmetry
classes for a one-gate intermediate, all 34 classes for two gates, and at least
232 of 234 classes for three gates. Lean checked the rule used to assess the
certificates. The full numerical classification still needs formal verification.
A separate search tried shortening the end of a known 28-gate construction. Some
cases timed out. They remain open.

**Other graph bounds.** For a 25-vertex, 48-edge graph, Lean established an
exact minimum of 59 gates when the circuit has syntactic degree at most one on
either side of the graph. Any 58-gate counterexample must therefore have degree
at least two on both sides. In a separate 42-vertex problem, Lean derived a
necessary condition for a proposed 19-gate circuit: under the step’s
restrictions, at least four matched gate positions must have a frequently read
endpoint. Neither result settles the unrestricted lower bound.

**Other assignments and dead ends.** The record also includes comparisons
between circuits with and without NOT gates on six-input functions, graph
edge-detection bounds, rectangle covers of binary matrices, and a
resolution-proof length question for five pigeons and four holes. One ten-by-ten
rectangle instance illustrates why attribution matters: our computation gave an
optimum of ten where the assignment requested nine. Another contributor had
already submitted the checker-accepted proof of the opposite statement. We
returned that assignment and claim no credit for their proof.
[Other contributor’s proof](https://github.com/open-goat/pequalnp-proofs/pull/13353)

## Final assignment and handoff

**Step 4697 asks about converting a circuit into a graph cover.** Every
non-isolated vertex in the graph has three neighbors, every cycle has length at
least seven, and the graph has at least one edge. The input switches select
vertices. A circuit with a budget of *s* gates says whether two selected
vertices share an edge. The task asks for another description of the same test:
build reusable sets of vertices by taking unions, then test pairs of sets. A
pair succeeds when each of its two sets contains a selected vertex. The required
budget is the number of stored unions plus twice the number of pairs, at most
*s* + 1.

**The mathematical obstacle.** In such a representation, a nonempty pair of sets
covers edges between its two sides. The sides must be disjoint, since selecting
one vertex cannot create an edge. If each side contained two vertices, the four
cross edges would give a forbidden four-cycle. Thus every useful pair has a
singleton side and describes a star. This observation narrows the shape of a
cover. What still needs proof is why an arbitrary small AND/OR/NOT circuit
guarantees a star representation within the same budget. The assignment was
released at wrap-up.

Lean also checked a counting bound for this star representation under explicit
overlap and availability assumptions. A stored union of two or more leaves can
be charged to at most one center. The project already has a stronger
graph-to-cover accounting theorem, L-meta-4695. The general circuit-to-cover
direction remains open in this record.
[Local counting lemma](work/StarCost4697.lean) ·
[Existing project theorem](../../lean/PEqualNP/Outside/L_meta_4695.lean)
