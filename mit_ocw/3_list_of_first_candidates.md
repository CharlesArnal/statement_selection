# Annotated MIT OCW Course List for Lean4 Autoformalization

This document lists all 140 courses in `mit_ocw/unzipped/`, annotated with their
candidacy for autoformalization in Lean4.

## Criteria

1. **Content Quality**: Course must have well-structured lecture notes or textbook PDFs
   (not just video transcripts, slides-only, problem sets only, or empty)
2. **Formalization Potential**: Course must cover mathematical content with clear
   theorems/definitions that could be formalized, and not be already well-represented
   in mathlib (basic calculus, basic linear algebra, basic group theory, basic topology,
   basic real analysis are mostly covered)

## Summary Statistics

| Status | Count |
|--------|-------|
| ✅ Good Candidate | 40 |
| ⚠️ Borderline Candidate | 19 |
| ❌ Not a Candidate | 81 |
| **Total** | **140** |

## Top-Tier Candidates

Courses with full textbook PDFs available and strong formalization value:

1. **18.745** - Lie Groups and Lie Algebras I (`mit18_745_f20_lec_full.pdf`)
2. **18.755** - Lie Groups and Lie Algebras II (`mit18_755_s24_lec_full.pdf`)
3. **18.757** - Representations of Lie Groups (`mit18_757_f23_lec_full.pdf`)
4. **18.785** - Number Theory I (`mit18_785f21_full_lec.pdf`)
5. **18.706** - Noncommutative Algebra (`mit18_706_s23_full_lec.pdf`)
6. **18.102** - Introduction to Functional Analysis (`MIT18_102s21_full_lec.pdf` + TeX)
7. **18-100A** - Real Analysis (`mit18_100af20_lec_full.pdf` + TeX)
8. **18.156** - Projection Theory (Differential Analysis II) (`mit18_156_s25_lec_full.pdf` + TeX)
9. **18.225** - Graph Theory and Additive Combinatorics (`mit18_225_f23_lec_full.pdf`)
10. **18.226** - Probabilistic Methods in Combinatorics (`mit18_226_f22_lec_full.pdf`)
11. **RES.18-012** - Algebra II Student Notes (`mit18_702s22_full_lec.pdf` + TeX)
12. **RES.18-015** - Topics in Fourier Analysis (`mitres_18_015_s24_full_lec.pdf`)
13. **18.238** - Geometry and Quantum Field Theory (`mit18_238_s23_lec_full.pdf`)
14. **18.S097** - Applied Category Theory (textbook PDF)

---

## Complete Course List

### Non-Math / Non-Formalizable Courses

**12.009J** | Undergraduate
*Theoretical Environmental Analysis*
Source: `12.009j-spring-2015`
Status: ❌ Not a Candidate
Reason: Earth science course (volcanoes, rivers, glaciers, ecosystems). Not mathematics.

**2.034J** | Graduate
*Nonlinear Dynamics and Waves*
Source: `2.034j-spring-2007`
Status: ❌ Not a Candidate
Reason: Mechanical engineering course. Only 6 PDFs, no lecture notes.

**3.021J** | Undergraduate
*Introduction to Modeling and Simulation*
Source: `3.021j-spring-2012`
Status: ❌ Not a Candidate
Reason: Materials science/engineering modeling course. Not pure mathematics.

**5.95J** | Graduate
*Teaching College-Level Science and Engineering*
Source: `5.95j-fall-2015`
Status: ❌ Not a Candidate
Reason: Pedagogy course about teaching methodology. Not mathematics content.

### Calculus & Basic Analysis (Too Basic / Already in Mathlib)

**18.01** | Undergraduate
*Single Variable Calculus*
Source: `18.01-fall-2006`
Status: ❌ Not a Candidate
Reason: Introductory single-variable calculus. Well-covered in mathlib. Content structure unclear (hash-prefixed filenames).

**18.013A** | Undergraduate
*Calculus with Applications*
Source: `18.013a-spring-2005`
Status: ❌ Not a Candidate
Reason: No PDF content at all. Empty static_resources.

**18.01SC** | Undergraduate
*Single Variable Calculus*
Source: `18.01sc-fall-2010`
Status: ❌ Not a Candidate
Reason: Introductory calculus, well-covered in mathlib. 841 PDFs but mostly session clips and video transcripts.

**18.02** | Undergraduate
*Multivariable Calculus*
Source: `18.02-fall-2007`
Status: ❌ Not a Candidate
Reason: Introductory multivariable calculus. Basics covered in mathlib. Mixed lecture/video content.

**18.022** | Undergraduate
*Calculus of Several Variables*
Source: `18.022-fall-2010`
Status: ❌ Not a Candidate
Reason: Introductory multivariable calculus variant. Basics covered in mathlib.

**18.024** | Undergraduate
*Multivariable Calculus with Theory*
Source: `18.024-spring-2011`
Status: ❌ Not a Candidate
Reason: Honors multivariable calculus. More rigorous but still fundamentally basic. Chapter notes available but content well-represented in mathlib.

**18.02SC** | Undergraduate
*Multivariable Calculus*
Source: `18.02sc-fall-2010`
Status: ❌ Not a Candidate
Reason: Introductory multivariable calculus, well-covered in mathlib. 513 PDFs but heavily video/recitation-based.

**RES.18-001** | Undergraduate
*Calculus Online Textbook*
Source: `res.18-001-fall-2023`
Status: ❌ Not a Candidate
Reason: Full calculus textbook (Gilbert Strang). Excellent content quality but covers basic calculus already in mathlib.

**RES.18-007** | Undergraduate
*Calculus Revisited: Multivariable Calculus*
Source: `res.18-007-fall-2011`
Status: ❌ Not a Candidate
Reason: Video-based multivariable calculus review. Too basic for formalization.

**RES.18-008** | Undergraduate
*Calculus Revisited: Complex Variables, Differential Equations, and Linear Algebra*
Source: `res.18-008-fall-2011`
Status: ❌ Not a Candidate
Reason: Video-based review course covering mixed introductory topics. Not deep enough for formalization.

**RES.18-006** | Undergraduate
*Calculus Revisited: Single Variable Calculus*
Source: `res.18-fall-2010`
Status: ❌ Not a Candidate
Reason: Video-based single variable calculus review. Too basic.

### Linear Algebra (Too Basic / Already in Mathlib)

**18.06** | Undergraduate
*Linear Algebra*
Source: `18.06-spring-2010`
Status: ❌ Not a Candidate
Reason: Introductory linear algebra (Strang). Well-covered in mathlib. Mostly video transcripts.

**18.065** | Undergraduate
*Matrix Methods in Data Analysis, Signal Processing, and Machine Learning*
Source: `18.065-spring-2018`
Status: ❌ Not a Candidate
Reason: Applied/computational matrix methods for ML. Mostly video transcripts. Low formalization potential.

**18.06CI** | Undergraduate
*Linear Algebra - Communications Intensive*
Source: `18.06ci-spring-2004`
Status: ❌ Not a Candidate
Reason: Writing-focused version of 18.06. Student projects and papers, not structured mathematical content.

**18.06SC** | Undergraduate
*Linear Algebra*
Source: `18.06sc-fall-2011`
Status: ❌ Not a Candidate
Reason: Introductory linear algebra, well-covered in mathlib. Session/video format.

**18.700** | Undergraduate
*Linear Algebra*
Source: `18.700-fall-2013`
Status: ❌ Not a Candidate
Reason: Abstract linear algebra. Only 18 PDFs (problem sets, no lecture notes). Basics in mathlib.

**RES.18-010** | Undergraduate
*A Vision of Linear Algebra*
Source: `res.18-010-spring-2020`
Status: ❌ Not a Candidate
Reason: Conceptual slides-based overview of linear algebra by Strang. Not suitable for formalization.

### Algebra (Undergraduate)

**18.702** | Undergraduate
*Algebra II*
Source: `18.702-spring-2011`
Status: ❌ Not a Candidate
Reason: Only 10 PDFs, all problem sets. No lecture notes. Insufficient content for extraction.

**18.703** | Undergraduate
*Modern Algebra*
Source: `18.703-spring-2013`
Status: ❌ Not a Candidate
Reason: Undergraduate group theory. 23 practice lectures but labeled "pra_l" suggesting presentation format. Basic algebra well-covered in mathlib.

**18.704** | Undergraduate
*Seminar in Algebra and Number Theory: Rational Points on Elliptic Curves*
Source: `18.704-fall-2004`
Status: ✅ Good Candidate
Reason: 65 well-structured lecture notes + 20 problem sets on elliptic curves. Student seminar write-ups provide detailed proofs. Elliptic curves theory not in mathlib.

**18.704** | Undergraduate
*Seminar in Algebra and Number Theory: Computational Commutative Algebra and Algebraic Geometry*
Source: `18.704-fall-2008`
Status: ❌ Not a Candidate
Reason: Only 1 PDF and 3 TeX files. Insufficient content.

**RES.18-011** | Non-Credit
*Algebra I Student Notes*
Source: `RES.18-011-fall-2021`
Status: ⚠️ Borderline Candidate
Reason: Excellent content quality - full textbook `mit18_701f21_full_lec.pdf` + 35 TeX source files. However, covers group theory and linear algebra largely present in mathlib. Some advanced topics (representations, symmetric/alternating groups) may have value.

**RES.18-012** | Undergraduate
*Algebra II Student Notes*
Source: `RES.18-012-spring-2022`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_702s22_full_lec.pdf` + 36 TeX source files. Covers rings, fields, and Galois theory. Galois theory formalization in mathlib is still incomplete. TeX sources make extraction straightforward.

### Real Analysis

**18.100A** | Undergraduate
*Real Analysis*
Source: `18-100a-fall-2020`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_100af20_lec_full.pdf` + 26 TeX source files + 43 lecture PDFs. Comprehensive real analysis with formal proofs. While basics of real analysis exist in mathlib, the textbook goes beyond (e.g., series, uniform convergence, metric space completeness). TeX availability is a major plus.

**18.100B** | Undergraduate
*Real Analysis*
Source: `18.100B-spring-2025`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_100b_s25_lec_full.pdf` + 24 lecture PDFs. Recent (Spring 2025) real analysis course with well-structured content. Complements 18-100A.

**18.100A** | Undergraduate
*Introduction to Analysis*
Source: `18.100a-fall-2012`
Status: ❌ Not a Candidate
Reason: Older version with only assignments + textbook corrections. No lecture notes. Use 18-100a-fall-2020 instead.

**18.100C** | Undergraduate
*Real Analysis*
Source: `18.100c-fall-2012`
Status: ⚠️ Borderline Candidate
Reason: 24 lecture summaries + problem sets. Well-structured lecture summaries (l1sum-l24sum) but summaries may lack full proofs. Older version; prefer 18-100A or 18.100B.

### Advanced Analysis & Functional Analysis

**18.101** | Undergraduate
*Analysis II*
Source: `18.101-fall-2005`
Status: ✅ Good Candidate
Reason: 41 well-structured lecture notes on analysis on manifolds (differential forms, Stokes' theorem, inverse/implicit function theorems). This material is largely MISSING from mathlib. Strong formalization potential.

**18.102** | Undergraduate
*Introduction to Functional Analysis*
Source: `18.102-spring-2021`
Status: ✅ Good Candidate
Reason: Full textbook `MIT18_102s21_full_lec.pdf` + 23 TeX source files + 25 lecture PDFs + 11 problem sets. Functional analysis (Banach/Hilbert spaces, spectral theory) has significant gaps in mathlib. Excellent content structure.

**18.103** | Undergraduate
*Fourier Analysis*
Source: `18.103-fall-2013`
Status: ✅ Good Candidate
Reason: Structured lecture materials on Fourier series, Fourier integrals, Lp theory, Brownian motion. 26 PDFs including topical notes (fseries1-3, fourierint1-2, lptheory, orthonormal). Fourier analysis is almost entirely MISSING from mathlib.

**18.125** | Graduate
*Measure and Integration*
Source: `18.125-fall-2003`
Status: ⚠️ Borderline Candidate
Reason: 24 lecture PDFs. Measure theory is already well-covered in mathlib (Lebesgue integration, measure spaces). May offer advanced content beyond what's formalized.

### Complex Analysis

**18.04** | Undergraduate
*Complex Variables with Applications*
Source: `18.04-spring-2018`
Status: ✅ Good Candidate
Reason: 14 well-structured topic notes (topic0-topic13) + 13 recitation handouts with solutions + 9 problem sets with solutions. Complex analysis is a MAJOR GAP in mathlib. Topics cover holomorphic functions, contour integration, residue theorem, conformal mappings.

**18.075** | Graduate
*Advanced Calculus for Engineers*
Source: `18.075-fall-2004`
Status: ⚠️ Borderline Candidate
Reason: Covers complex analysis and ODEs. "For Engineers" suggests applied focus, but lecture notes contain rigorous content. May overlap with 18.04 and 18.112.

**18.112** | Undergraduate
*Functions of a Complex Variable*
Source: `18.112-fall-2008`
Status: ✅ Good Candidate
Reason: 23 lecture PDFs on advanced complex analysis. Graduate-level treatment going beyond 18.04. Complex analysis is a major gap in mathlib.

**18.117** | Graduate
*Topics in Several Complex Variables*
Source: `18.117-spring-2005`
Status: ✅ Good Candidate
Reason: 38 lecture notes + 4 problem sets. Several complex variables theory. Specialized and entirely absent from mathlib.

### Differential Equations & PDEs

**18.031** | Undergraduate
*System Functions and the Laplace Transform*
Source: `18.031-spring-2019`
Status: ❌ Not a Candidate
Reason: Only 5 PDFs (all appear to be duplicate video transcripts). No lecture content.

**18.152** | Undergraduate
*Introduction to Partial Differential Equations*
Source: `18.152-fall-2011`
Status: ✅ Good Candidate
Reason: 18 lecture PDFs + 12 problem sets. Well-structured intro to PDEs. PDEs are almost entirely MISSING from mathlib. Covers Laplace/heat/wave equations, existence and uniqueness theorems.

**18.155** | Graduate
*Differential Analysis*
Source: `18.155-fall-2004`
Status: ⚠️ Borderline Candidate
Reason: Has 16 section notes (section1-16) + 1 full lecture_notes.pdf + 8 problem sets. Content present but organization is section-based rather than lecture-based. Distribution theory, Sobolev spaces.

**18.156** | Graduate
*Differential Analysis*
Source: `18.156-spring-2004`
Status: ❌ Not a Candidate
Reason: Only 12 lecture PDFs with terse naming (da5, da10, lec9). Older course. Prefer 18.156-spring-2025.

**18.156** | Graduate
*Projection Theory*
Source: `18.156-spring-2025`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_156_s25_lec_full.pdf` + 49 lecture PDFs + 6 TeX files + 5 problem sets. Most recent course (Spring 2025). Covers pseudodifferential operators, microlocal analysis. Entirely absent from mathlib.

**18.303** | Undergraduate
*Linear Partial Differential Equations*
Source: `18.303-fall-2006`
Status: ❌ Not a Candidate
Reason: 47 PDFs but disorganized naming (ProbQuasi, probwave1, etc.). Older version; prefer 18.303-fall-2014.

**18.303** | Undergraduate
*Linear Partial Differential Equations: Analysis and Numerics*
Source: `18.303-fall-2014`
Status: ⚠️ Borderline Candidate
Reason: Well-structured. But "Analysis and Numerics" suggests significant computational content alongside theory. PDE theory parts are formalizable.

**18.306** | Graduate
*Advanced Partial Differential Equations with Applications*
Source: `18.306-fall-2009`
Status: ✅ Good Candidate
Reason: 35 lecture PDFs + 12 problem sets. Well-structured advanced PDE theory. Covers nonlinear PDEs, characteristics, weak solutions. PDEs are a major gap in mathlib.

### Probability & Statistics

**18.05** | Undergraduate
*Introduction to Probability and Statistics*
Source: `18.05-spring-2022`
Status: ❌ Not a Candidate
Reason: 181 PDFs but heavily class-activity based (class prep + pset format). Introductory probability/statistics with applied focus. Low formalization potential.

**18.175** | Graduate
*Theory of Probability*
Source: `18.175-spring-2014`
Status: ✅ Good Candidate
Reason: 38 lecture PDFs + 3 problem sets. Graduate probability theory (measure-theoretic). Covers convergence theorems, CLT, martingales. Probability theory has significant gaps in mathlib (CLT, LLN not formalized).

**18.177** | Graduate
*Universal Random Structures in 2D*
Source: `18.177-fall-2015`
Status: ❌ Not a Candidate
Reason: Only 3 PDFs (intro, open problems, lecture notes). Too sparse despite interesting topic.

**18.440** | Undergraduate
*Probability and Random Variables*
Source: `18.440-spring-2014`
Status: ❌ Not a Candidate
Reason: Introductory probability. 37 lectures + 10 problem sets but content is too basic for formalization. Largely covered by mathlib's measure-theoretic foundations.

**18.465** | Graduate
*Topics in Statistics: Nonparametrics and Robustness*
Source: `18.465-spring-2005`
Status: ❌ Not a Candidate
Reason: 22 PDFs. Statistics course with applied focus. No clear lecture structure.

**18.465** | Graduate
*Topics in Statistics: Statistical Learning Theory*
Source: `18.465-spring-2007`
Status: ❌ Not a Candidate
Reason: 34 lectures on statistical learning theory. Applied/ML-adjacent. Low formalization potential.

**18.600** | Undergraduate
*Probability and Random Variables*
Source: `18.600-fall-2019`
Status: ❌ Not a Candidate
Reason: Introductory probability (replacement for 18.440). 38 lectures but too basic. Same content level as 18.440.

**18.650** | Undergraduate
*Statistics for Applications*
Source: `18.650-fall-2016`
Status: ❌ Not a Candidate
Reason: Applied statistics. Mostly video transcripts. Low formalization potential.

**18.657** | Graduate
*Mathematics of Machine Learning*
Source: `18.657-fall-2015`
Status: ❌ Not a Candidate
Reason: ML theory course. Only labeled lectures are generic. Applied focus.

**18.S997** | Graduate
*High-Dimensional Statistics*
Source: `18.s997-spring-2015`
Status: ❌ Not a Candidate
Reason: Has course notes PDF but covers statistical methods. Applied focus, low formalization potential.

### Algebra & Number Theory (Graduate)

**18.705** | Graduate
*Commutative Algebra*
Source: `18.705-fall-2008`
Status: ❌ Not a Candidate
Reason: Only 2 PDFs. Insufficient content.

**18.706** | Graduate
*Noncommutative Algebra*
Source: `18.706-spring-2023`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_706_s23_full_lec.pdf` + 28 lecture PDFs + 6 problem sets. Noncommutative ring theory, module theory. Substantial content not in mathlib. Well-structured.

**18.725** | Graduate
*Algebraic Geometry*
Source: `18.725-fall-2015`
Status: ✅ Good Candidate
Reason: 26 lecture notes + 11 problem sets. Foundations of algebraic geometry (varieties, morphisms, sheaves). Algebraic geometry is mostly ABSENT from mathlib. Well-structured lecture notes.

**18.726** | Graduate
*Algebraic Geometry*
Source: `18.726-spring-2009`
Status: ✅ Good Candidate
Reason: 27 lecture notes + 12 problem sets. Advanced algebraic geometry (cohomology, Riemann-Roch, Serre duality, GAGA). Descriptive filenames. Continues 18.725.

**18.727** | Graduate
*Topics in Algebraic Geometry: Intersection Theory on Moduli Spaces*
Source: `18.727-spring-2006`
Status: ⚠️ Borderline Candidate
Reason: 10 PDFs with topic-based names (picard, kontsevich, homology, generaltype). Very specialized. Well-structured but niche.

**18.735** | Graduate
*Double Affine Hecke Algebras in Representation Theory, Combinatorics, Geometry, and Mathematical Physics*
Source: `18.735-fall-2009`
Status: ✅ Good Candidate
Reason: 10 chapter PDFs (ch01-ch10) + 1 full lecture PDF. Textbook-style chapter structure. Specialized but well-organized content on Hecke algebras. Not in mathlib.

**18.745** | Graduate
*Lie Groups and Lie Algebras I*
Source: `18.745-fall-2020`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_745_f20_lec_full.pdf` + 27 individual lecture PDFs. Lie theory has significant gaps in mathlib. Excellent structure.

**18.755** | Graduate
*Lie Groups and Lie Algebras II*
Source: `18.755-spring-2024`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_755_s24_lec_full.pdf` + 26 lecture PDFs. Continuation of 18.745. Lie theory gaps in mathlib. Well-structured.

**18.757** | Graduate
*Representations of Lie Groups*
Source: `18.757-fall-2023`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_757_f23_lec_full.pdf` + 32 lecture PDFs. Representation theory of Lie groups. Missing from mathlib. Well-structured.

**18.769** | Graduate
*Topics in Lie Theory: Tensor Categories*
Source: `18.769-spring-2009`
Status: ✅ Good Candidate
Reason: 13 well-structured lecture PDFs on tensor categories. Category-theoretic content. Tensor categories not in mathlib.

**18.782** | Undergraduate
*Introduction to Arithmetic Geometry*
Source: `18.782-fall-2013`
Status: ✅ Good Candidate
Reason: 25 lecture notes + 11 problem sets. Arithmetic geometry covering schemes, number fields, zeta functions. Well-structured. Not in mathlib.

**18.783** | Undergraduate
*Elliptic Curves*
Source: `18.783-spring-2021`
Status: ✅ Good Candidate
Reason: 25 detailed lecture notes + 9 slides + 12 problem sets + 12 TeX files. Comprehensive elliptic curves course. Has both notes and slides. Computational aspects exist but theoretical content is strong. Not in mathlib.

**18.785** | Graduate
*Number Theory I*
Source: `18.785-fall-2021`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_785f21_full_lec.pdf` + 36 individual lecture notes + 11 problem sets. Algebraic number theory. Excellent structure. Number theory has gaps in mathlib.

**18.786** | Graduate
*Topics in Algebraic Number Theory*
Source: `18.786-spring-2010`
Status: ⚠️ Borderline Candidate
Reason: 12 lecture PDFs + 11 problem sets. Less content than 18.785. Older.

**18.786** | Graduate
*Number Theory II: Class Field Theory*
Source: `18.786-spring-2016`
Status: ✅ Good Candidate
Reason: 24 lecture notes + 9 problem sets. Class field theory is an important area not in mathlib. Well-structured.

### Topology & Geometry

**18.900** | Undergraduate
*Geometry and Topology in the Plane*
Source: `18.900-spring-2023`
Status: ⚠️ Borderline Candidate
Reason: 40 lectures + 40 quizzes. Very well-structured (lec1-lec40, q1-q40). However, this is an undergraduate intro course. Content may be too elementary.

**18.901** | Undergraduate
*Introduction to Topology*
Source: `18.901-fall-2004`
Status: ❌ Not a Candidate
Reason: 15 PDFs. Basic point-set topology largely covered in mathlib (topological spaces, compactness, connectedness).

**18.904** | Undergraduate
*Seminar in Topology*
Source: `18.904-spring-2011`
Status: ❌ Not a Candidate
Reason: Only 10 PDFs. Sparse content. Seminar format.

**18.905** | Graduate
*Algebraic Topology I*
Source: `18.905-fall-2016`
Status: ✅ Good Candidate
Reason: 39 lecture PDFs + 6 problem sets. Algebraic topology (fundamental group, homology, cohomology). AT is largely MISSING from mathlib. Well-structured lecture notes.

**18.906** | Graduate
*Algebraic Topology II*
Source: `18.906-spring-2020`
Status: ✅ Good Candidate
Reason: 5 chapter PDFs (ch1-ch5) + notes + spectral sequences references + 6 problem sets. Textbook-style chapter organization. Covers spectral sequences, higher homotopy theory. Continues 18.905.

**18.915** | Graduate
*Graduate Topology Seminar: Kan Seminar*
Source: `18.915-fall-2014`
Status: ❌ Not a Candidate
Reason: Only 3 PDFs (reading list, Steenrod operations, 1 transcript). Seminar format with no structured lecture content.

**18.917** | Graduate
*Topics in Algebraic Topology: The Sullivan Conjecture*
Source: `18.917-fall-2007`
Status: ✅ Good Candidate
Reason: 38 detailed lecture PDFs covering the Sullivan conjecture. Specialized but comprehensive. Well-structured. Not in mathlib.

**18.950** | Undergraduate
*Differential Geometry*
Source: `18.950-fall-2008`
Status: ❌ Not a Candidate
Reason: 14 PDFs but only problem sets + a few revised chapter notes. No systematic lecture notes.

**18.965** | Graduate
*Geometry of Manifolds*
Source: `18.965-fall-2004`
Status: ✅ Good Candidate
Reason: 26 lecture PDFs on differential geometry of manifolds. Riemannian geometry, connections, curvature. Differential geometry is largely ABSENT from mathlib.

**18.966** | Graduate
*Geometry of Manifolds*
Source: `18.966-spring-2007`
Status: ✅ Good Candidate
Reason: 25 lecture PDFs + 6 problem sets. Continuation of 18.965. Covers Hodge theory, characteristic classes. Not in mathlib.

**18.969** | Graduate
*Topics in Geometry: Dirac Geometry*
Source: `18.969-fall-2006`
Status: ⚠️ Borderline Candidate
Reason: 16 lecture PDFs + 6 problem sets. Specialized topic (Dirac structures, generalized geometry). Well-structured but very niche.

**18.969** | Graduate
*Topics in Geometry: Mirror Symmetry*
Source: `18.969-spring-2009`
Status: ⚠️ Borderline Candidate
Reason: 25 lecture PDFs. Mirror symmetry at the interface of geometry and physics. Well-structured but extremely specialized.

**18.994** | Undergraduate
*Seminar in Geometry*
Source: `18.994-fall-2004`
Status: ✅ Good Candidate
Reason: 19 chapters (chapter1-19) in textbook format + 6 problem sets + compiled full document. Student-written but well-organized. Covers curves and surfaces.

### Combinatorics & Discrete Mathematics

**18.218** | Graduate
*Topics in Combinatorics: Analysis of Boolean Functions*
Source: `18-218-spring-2021`
Status: ✅ Good Candidate
Reason: 13 well-structured lecture PDFs + 5 problem sets. Analysis of Boolean functions (Fourier analysis on Boolean cube). Clean naming. Not in mathlib.

**18.225** | Graduate
*Graph Theory and Additive Combinatorics*
Source: `18.225-fall-2023`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_225_f23_lec_full.pdf` + individual lectures + 1 problem set. Yufei Zhao's course. Excellent structure. Combinatorics has gaps in mathlib.

**18.226** | Graduate
*Probabilistic Methods in Combinatorics*
Source: `18.226-fall-2022`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_226_f22_lec_full.pdf` + individual lectures. Probabilistic method (Lovasz Local Lemma, random graphs). Well-structured. Not in mathlib.

**18.304** | Undergraduate
*Undergraduate Seminar in Discrete Mathematics*
Source: `18.304-spring-2015`
Status: ❌ Not a Candidate
Reason: Only 2 PDFs + 3 TeX files. Insufficient content. Student project format.

**18.310** | Undergraduate
*Principles of Discrete Applied Mathematics*
Source: `18.310-fall-2013`
Status: ❌ Not a Candidate
Reason: 58 PDFs but mostly problem sets (20) and pre-recorded content. Applied discrete math. No clear lecture notes.

**18.315** | Graduate
*Combinatorial Theory: Hyperplane Arrangements*
Source: `18.315-fall-2004`
Status: ❌ Not a Candidate
Reason: Only 12 PDFs with 6 lectures. Too sparse.

**18.315** | Graduate
*Combinatorial Theory: Introduction to Graph Theory, Extremal and Enumerative Combinatorics*
Source: `18.315-spring-2005`
Status: ✅ Good Candidate
Reason: 38 lecture PDFs + 8 problem sets. Comprehensive graduate combinatorics. Well-structured. Graph theory and enumerative combinatorics not well-represented in mathlib.

**18.318** | Graduate
*Topics in Algebraic Combinatorics*
Source: `18.318-spring-2006`
Status: ❌ Not a Candidate
Reason: Only 10 PDFs. Sparse content. Few notes files.

**18.319** | Graduate
*Geometric Combinatorics*
Source: `18.319-fall-2005`
Status: ❌ Not a Candidate
Reason: Only 13 PDFs. Sparse. Student presentation format.

**18.S997** | Graduate
*The Polynomial Method*
Source: `18.s997-fall-2012`
Status: ✅ Good Candidate
Reason: 34 lecture PDFs + 4 problem sets. Covers the polynomial method in combinatorics (Dvir's theorem, joints problem, etc.). Well-structured. Not in mathlib.

### Computer Science / Algorithms

**18.404J** | Undergraduate
*Theory of Computation*
Source: `18.404j-fall-2020`
Status: ⚠️ Borderline Candidate
Reason: 25 lecture PDFs + 6 homework sets. Sipser's TCS course. Well-structured. Computability/complexity theory has some formalization potential but is primarily CS.

**18.408** | Graduate
*Topics in Theoretical Computer Science: Probabilistically Checkable Proofs*
Source: `18.408-fall-2022`
Status: ⚠️ Borderline Candidate
Reason: 13 lecture PDFs on PCP theorem and hardness of approximation. Specialized TCS topic with mathematical depth. Well-structured.

**18.409** | Graduate
*Topics in Theoretical Computer Science: An Algorithmist's Toolkit*
Source: `18.409-fall-2009`
Status: ❌ Not a Candidate
Reason: 33 PDFs but mostly scribe notes with inconsistent naming. Toolkit/survey format.

**18.409** | Graduate
*Behavior of Algorithms*
Source: `18.409-spring-2002`
Status: ❌ Not a Candidate
Reason: 18 lecture PDFs. Analysis of algorithm behavior. Applied CS.

**18.413** | Undergraduate
*Error-Correcting Codes Laboratory*
Source: `18.413-spring-2004`
Status: ❌ Not a Candidate
Reason: Lab course on coding theory. 16 lecture PDFs but lab-oriented. Mixed student project content.

**18.417** | Graduate
*Introduction to Computational Molecular Biology*
Source: `18.417-fall-2004`
Status: ❌ Not a Candidate
Reason: Computational biology. Not pure mathematics.

**18.433** | Undergraduate
*Combinatorial Optimization*
Source: `18.433-fall-2003`
Status: ❌ Not a Candidate
Reason: 17 PDFs with terse naming (l1, l18, l20). Optimization algorithms. Applied.

**18.435J** | Graduate
*Quantum Computation*
Source: `18.435j-fall-2003`
Status: ❌ Not a Candidate
Reason: Quantum computing. 10 lectures + 5 problem sets. Physics-adjacent. Low pure math formalization value.

**18.997** | Graduate
*Topics in Combinatorial Optimization*
Source: `18.997-spring-2004`
Status: ⚠️ Borderline Candidate
Reason: 22 lecture PDFs on combinatorial optimization. Well-structured. Some mathematical content (matroid theory, polyhedral combinatorics) but applied focus.

**6.042J** | Undergraduate
*Mathematics for Computer Science*
Source: `6.042j-spring-2015`
Status: ⚠️ Borderline Candidate
Reason: Full textbook `mit6_042js15_textbook.pdf` + 36 session PDFs. Excellent structure. However, covers basic discrete math (logic, induction, graph theory, probability) mostly at introductory level.

**6.045J** | Undergraduate
*Automata, Computability, and Complexity*
Source: `6.045j-spring-2011`
Status: ⚠️ Borderline Candidate
Reason: 23 lecture PDFs. Theory of computation. Some formalization value (automata theory, decidability) but primarily CS content.

**6.046J** | Undergraduate
*Introduction to Algorithms (SMA 5503)*
Source: `6.046j-fall-2005`
Status: ❌ Not a Candidate
Reason: Algorithms course (CLRS-style). 19 lectures. Applied/computational focus. Low formalization potential for pure math.

**6.046J** | Undergraduate
*Design and Analysis of Algorithms*
Source: `6.046j-spring-2015`
Status: ⚠️ Borderline Candidate
Reason: 45 lectures + 20 problem sets. Well-structured. Correctness proofs could be formalized, but primarily algorithmic rather than mathematical.

**6.852J** | Graduate
*Distributed Algorithms*
Source: `6.852j-fall-2009`
Status: ❌ Not a Candidate
Reason: Distributed systems algorithms. CS course, not pure math.

**6.854J** | Graduate
*Advanced Algorithms*
Source: `6.854j-fall-2008`
Status: ❌ Not a Candidate
Reason: Advanced algorithms (linear programming, approximation). CS/applied focus.

**6.856J** | Graduate
*Randomized Algorithms*
Source: `6.856j-fall-2002`
Status: ❌ Not a Candidate
Reason: Randomized algorithms. Mostly problem sets, no clear lecture structure. CS focus.

### Applied / Computational Mathematics

**18.085** | Undergraduate
*Computational Science and Engineering I*
Source: `18.085-summer-2020`
Status: ❌ Not a Candidate
Reason: Computational/applied course. Lecture PDFs but focused on numerical methods.

**18.305** | Graduate
*Advanced Analytic Methods in Science and Engineering*
Source: `18.305-fall-2004`
Status: ❌ Not a Candidate
Reason: Applied methods course. 25 PDFs with section-based names. Methods for physics/engineering applications.

**18.330** | Undergraduate
*Introduction to Numerical Analysis*
Source: `18.330-spring-2012`
Status: ❌ Not a Candidate
Reason: Numerical analysis. 7 lecture PDFs + 8 homework sets. Computational focus.

**18.335J** | Graduate
*Introduction to Numerical Methods*
Source: `18.335j-spring-2019`
Status: ❌ Not a Candidate
Reason: Numerical methods. 24 lectures. Computational focus.

**18.336** | Graduate
*Numerical Methods for Partial Differential Equations*
Source: `18.336-spring-2009`
Status: ❌ Not a Candidate
Reason: Numerical PDE methods. 25 lectures. Computational focus.

**18.337J** | Graduate
*Parallel Computing*
Source: `18.337j-fall-2011`
Status: ❌ Not a Candidate
Reason: Only 5 PDFs (presentations). CS/computing topic.

**18.353J** | Undergraduate
*Nonlinear Dynamics I: Chaos*
Source: `18.353j-fall-2012`
Status: ❌ Not a Candidate
Reason: Applied dynamical systems. Only problem sets (9), no lecture notes. Chaos theory has limited formalization potential.

**18.369** | Graduate
*Mathematical Methods in Nanophotonics*
Source: `18.369-spring-2008`
Status: ❌ Not a Candidate
Reason: Applied physics/photonics. 13 PDFs, mostly problem sets. Not pure math.

**18.385J** | Graduate
*Nonlinear Dynamics and Chaos*
Source: `18.385j-fall-2014`
Status: ❌ Not a Candidate
Reason: Applied dynamical systems. Only 1 lecture note + 10 problem sets. Limited content.

**18.642** | Undergraduate
*Topics in Mathematics with Applications in Finance*
Source: `18.642-fall-2024`
Status: ❌ Not a Candidate
Reason: Mathematical finance. 36 lectures but heavily applied. Video transcripts. Low formalization potential.

**18.S096** | Undergraduate
*Topics in Mathematics with Applications in Finance*
Source: `18.s096-fall-2013`
Status: ❌ Not a Candidate
Reason: Mathematical finance. 23 lectures + case studies. Applied.

**18.S096** | Undergraduate
*Topics in Mathematics of Data Science*
Source: `18.s096-fall-2015`
Status: ❌ Not a Candidate
Reason: Data science mathematics. Sessions + open problems format. Applied.

**18.S096** | Undergraduate
*Matrix Calculus for Machine Learning and Beyond*
Source: `18.s096-iap-2023`
Status: ❌ Not a Candidate
Reason: Has full lecture notes but covers matrix calculus for ML applications. Applied focus.

### Dynamical Systems / Physics-Adjacent

**18.238** | Graduate
*Geometry and Quantum Field Theory*
Source: `18.238-Spring-2023`
Status: ✅ Good Candidate
Reason: Full textbook `mit18_238_s23_lec_full.pdf` + weekly lecture PDFs (week01-week13). Mathematical QFT covering formal algebraic structures. Well-structured. Not in mathlib.

### Special Topics / Seminars

**18.091** | Undergraduate
*Mathematical Exposition*
Source: `18.091-spring-2005`
Status: ❌ Not a Candidate
Reason: Course about mathematical writing, not mathematical content.

**18.098** | Undergraduate
*Street-Fighting Mathematics*
Source: `18.098-january-iap-2008`
Status: ❌ Not a Candidate
Reason: Estimation and approximation techniques. Not formal mathematics.

**18.104** | Undergraduate
*Seminar in Analysis: Applications to Number Theory*
Source: `18.104-fall-2006`
Status: ❌ Not a Candidate
Reason: Only 12 PDFs. Student seminar presentations. Scattered topics.

**18.821** | Undergraduate
*Project Laboratory in Mathematics*
Source: `18.821-spring-2013`
Status: ❌ Not a Candidate
Reason: Project-based course. Student papers and presentations, not structured mathematical content.

**18.S191** | Undergraduate
*Introduction to Computational Thinking*
Source: `18.S191-fall-2022`
Status: ❌ Not a Candidate
Reason: No PDF content. Computational thinking with Julia. Not pure math.

**18.A34** | Undergraduate
*Mathematical Problem Solving (Putnam Seminar)*
Source: `18.a34-fall-2018`
Status: ❌ Not a Candidate
Reason: Competition problem solving. 11 problem sets + 11 supplementary materials. Not structured for formalization.

**18.S190** | Undergraduate
*Introduction to Metric Spaces*
Source: `18.s190-iap-2023`
Status: ❌ Not a Candidate
Reason: Short IAP course. Only 6 lectures. Too brief. Metric spaces basics are in mathlib.

**18.S190** | Undergraduate
*Introduction to Computational Thinking with Julia, with Applications to Modeling the COVID-19 Pandemic*
Source: `18.s190-spring-2020`
Status: ❌ Not a Candidate
Reason: No PDF content. Computational Julia course.

**RES.18-004** | Undergraduate
*The Torch or The Firehose: A Guide to Section Teaching*
Source: `res.18-004-spring-2009`
Status: ❌ Not a Candidate
Reason: Teaching guide, not mathematical content.

**RES.18-015** | Non-Credit
*Topics in Fourier Analysis*
Source: `res.18-015-spring-2024`
Status: ✅ Good Candidate
Reason: Full textbook `mitres_18_015_s24_full_lec.pdf` + 25 lecture PDFs. Fourier analysis resource. Fourier analysis is almost entirely missing from mathlib. Well-structured.

### Category Theory

**18.S097** | Undergraduate
*Applied Category Theory*
Source: `18.s097-january-iap-2019`
Status: ✅ Good Candidate
Reason: Has textbook `18-s097iap19textbook.pdf` + chapter PDFs + 3 problem sets. Category theory has gaps in mathlib. Textbook format is ideal for extraction.

**18.S996** | Graduate
*Category Theory for Scientists*
Source: `18.s996-spring-2013`
Status: ⚠️ Borderline Candidate
Reason: Has textbook `MIT18_S996S13_textbook.pdf`. However, "for Scientists" suggests applied focus. Category theory is partially in mathlib. May have novel organizational/applied perspectives.

### Random Matrix Theory / Model Theory

**18.996** | Graduate
*Topics in Theoretical Computer Science : Internet Research Problems*
Source: `18.996-spring-2002`
Status: ❌ Not a Candidate
Reason: Internet/web research problems. CS applied course.

**18.996** | Graduate
*Random Matrix Theory and Its Applications*
Source: `18.996-spring-2004`
Status: ❌ Not a Candidate
Reason: 83 PDFs but mostly research papers and student project files. No clear lecture note structure. Poorly organized for extraction.

**18.996A** | Graduate
*Simplicity Theory*
Source: `18.996a-spring-2004`
Status: ⚠️ Borderline Candidate
Reason: 13 lecture PDFs. Model theory / simplicity theory. Well-structured but very specialized and niche.
