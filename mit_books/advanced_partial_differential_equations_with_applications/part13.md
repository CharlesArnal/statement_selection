18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 13 2009 10 21 WED

TOPICS: Shallow water and higher order terms. Traveling waves, shocks, and the effects of dispersion. Solitons. Small dispersion limit.

Continue and finish material in lecture 12. In particular: % Traveling wave solutions for KdV: u\_t + (0.5\*u^2)\_x = epsilon^2\*u\_xxx.

Can write them exactly, but easier to do it with phase plane analysis. Periodic traveling waves and solitary waves. No shocks.

What happens in the epsilon small limit? Smooth I.V. should start evolving as u\_t + u\*u\_x = 0, approximately. But this then produces short scales, and the term epsilon^2\*u\_xxx kicks

 in (preventing multiple values). However, no shocks can form (there are

 none in this equation). What one observes is that short wave oscillations

 [wave-length O(epsilon)] are generated near the points where u\_t + u\*u\_x = 0 would produce infinite derivatives. These oscillations propagate away from these points, and the region with fast variations in the solution grows with time. No easy fix for cases like this. The small scales cannot be ignored (and shoved into a discontinuity) as in the cases where shocks form.