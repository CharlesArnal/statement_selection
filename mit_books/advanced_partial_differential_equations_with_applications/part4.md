18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

```
Lecture 04 2009 09 21 MON
```

TOPICS: First order scalar pde. Examples of solutions by characteristics. Domain of influence.

Review characteristics.

Examples in detail:

1) x\*u\_x + y\*u\_y = 0,

for y >= 1, with u(x, 1) = F(x)

2) x\*u\_x + y\*u\_y = 1+y^2,

for y >= 1, with u(x, 1) = F(x)

Domain of dependence and domain of influence. Where is the solution defined and where it is not.

Examples showing solution not unique outside domain of influence:

For case (1), with F(x) = exp(-x^2), consider (in the plane without the origin = P0)

u1 = exp(-x^2/y^2) ................. for x^2+y^2 > 0.

u = exp(-x^2/y^2) .................. for y >= 0 and x^2+y^2 > 0. = exp(-3\*x^2/y^2) ................ for y <=0 and x^2+y^2 > 0.

Both u1 and u2 are smooth and solve the equation and given data, but they are not equal outside y >= 0 and x^2+y^2 > 0. Can construct infinitely many such u's.