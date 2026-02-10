18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

## Lecture 01 2009 09 09 WED

TOPICS: Mechanics of the course.

Example pde. Initial and boundary value problems.

Well and ill-posed problems.

Introduction: Syllabus issues; exams; lecturer; etc.

ODE's and PDE's

ODE solution: determined by a set of constants. Simple Examples. PDE solution: determined by functions. Simple Examples.

Example pde: heat, laplace, wave, ... more later.

Initial value and boundary value problems.

Quote existence-uniqueness theorem for ODE IV problem.

No analogous theorem for PDE's. Closest is C-K theorem, and need very strong restrictions (e.g.: analytic functions.)

Well and ill-posed problems. Why is this important.

Examples (show these are badly ill-posed: growth rate of perturbations goes to infinity as the frequency grows. No control over errors.

- --- Can you recover the temperature in the past from today's data?
- --- Can you recover the steady state temperature inside a body from knowledge of the temperature and heat flux along some part of the boundary? [Do example of square, with temperature and flux given on a side, zero temperature on the two adjoining sides, and nothing known about the opposite side].
- --- Real life: issues like this (open problems) appear in multi-phase flows modeling, phase transition modeling, detonation waves (square wave model), image reconstruction.
- Possible Fix: filtering. Works if filtering makes sense within context of problem (e.g. CAT scans or image reconstruction). It can also lead to nonsense if applied mechanically.