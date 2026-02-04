## Overview
I have gathered several mathematical textbooks, each under the format of a folder containing various tex files, pdfs and other files.
Our main goal is to extract every mathematical statement in each of these textbooks, and to assess whether it is already present in mathlib.

## Details

# Where are the textbooks

The textbooks are found in folders with names such as statement_selection/algebraic_topology_1 or statement_selection/algebraic_geometry. Each folder corresponds to a single textbook. The folder contains the material constituting the textbook, along with some additional files that are used to display the textbook on a website and can ignored.

# What constitutes a statement

A statement is any mathematical fact stated as either a lemma, a proposition, a theorem, or some other synonym of these notions in the textbooks. They are almost always stated with a name that explicitly states their nature, such as "Lemma 3.2" or "Theorem 4.1".

# What to do

When asked to process a textbook, you must:
- Start reading the textbook from the start, and process each statement one after the other. As the textbooks can be very long, do not read the textbooks all at once. Rather, read them by chunks of a few pages and process one statement after the other. Finish processing all the statements in a chunk before moving on to the next one.
- For each statement that you encounter:
1) You must add it to a file called "all_statements.md", which you will place in the folder corresponding to the textbook. If a statement has a name such as "Lemma 3.1 [Yoneda's lemma]", report the entire name, including the statement's "nickname".
2. You must thoroughly search mathlib, which can be found at statement_selection/mathlib, to see if it is already present in mathlib. You must not only use regex: you must actually read the files that seem relevant. If a statement is not stated exactly as it is in mathlib, but if it is essentially equivalent to one or several existing statements, we still consider that it is already present in mathlib.
3. After having determined whether the statement is already in mathlib, you must report your conclusions in two files that will also be placed in the folder corresponding to the texstbook: one is called detailed_assessment.md, the other short_assessment.md. In short_assessment.md, you only list the statements and write after each one "included" or "non-included" depending on whether it is already in mathlib, like so:

Lemma 3.1:
non-included
Proposition 3.2:
included

In detailed_assessment.md, you must also give a one-paragraph explanation of your assessment: if the statement is in mathlib, you must point to the statement or statements that are equivalent to it. If it is not in mathlib, you must explain where you searched, and how the current content is different from it. Like so:

Lemma 3.1:
included
Corresponds to lemma leadingCoeff_preΨ' from statement_selection/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean

4) Once you are done processing a statement, you can move on to the next statement.

# Notes:
It is important that you do not rely on regex and search patterns only, but also read the mathlib files to make your conclusions robust.


