MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 1

#### DENIS AUROUX

Goal of the class: this is not always going to be the most rigorous class, but the goal is to tell the story of mirror symmetry.

### 1. Physical Origins

Mirror symmetry comes from statements in supersymmetric string theory. Basic idea of string theory: replace particles with vibrating strings, which propogate through space and form surfaces. We thus get 2-d quantum field theories on these surfaces, called *worldsheets*, with the fields taking values in some manifolds. Supersymmetric means that there are lots of symmetries acting here, and physicists have lots of buzzwords here that won't make sense to mathematicians. For instance "superconformal field theory" means that the theory depends only on the conformal structure on  $\Sigma$  rather than the Riemannian structure. There are various flavors of these theories, but the ones more relevant to mirror symmetry are the *nonlinear sigma-models* 

1.1. **Non-linear Sigma Models.** Here, we look at maps  $\phi : \Sigma \to X$ , where X (the "target space") is a Calabi-Yau manifold.

**Definition 1.** A Calabi-Yau manifold is a complex manifold (X, J) (ideally, compact, 3-dimensional, maybe  $b_1 = 0$ ) s.t.  $K_X = \bigwedge^n T^*X \cong \mathcal{O}_X$ , so  $\exists$  a section  $\Omega \in H^0(X, K_X)$ , i.e. a holomorphic volume form.

On this manifold, we have a complexified Kähler form  $\omega^{\mathbb{C}} = B + i\omega$  which is a closed (1, 1)-form and Im  $\omega^{\mathbb{C}} = \omega$  is nondegenerate (B is supposed to make the space of symplectic forms a subspace of complex cohomology). The "moduli" of the theory, i.e. how one can deform the complex structure J and the complexified symplectic structure  $\omega^{\mathbb{C}}$ , is governed by  $H^1(X, T_X)$  and  $H^{1,1}(X) = H^1(X, \Omega_X^1)$  respectively.

More physics: the field theory is governed by a really big lie algebra, but two of the interesting generators  $(Q, \overline{Q})$  are called "supersymmetric charges": each particles is assigned some eigenvalue of these indicating its charge. We have simultaneous eigenspaces  $H^q(X, \Omega^p TX), H^q(X, \Omega_X^p)$ . But many of our choices here are arbitrary: for instance, we should be able to replace Q with -Q, which exchanges these two eigenspaces. Thus, we have an idea that for any target

space on which superstring theory acts, these two spaces (a priori of different dimension) are the opposite spaces for a different target space (the "mirror").

**Conjecture 1.** Given a Calabi-Yau manifold  $(X, J, \omega^{\mathbb{C}})$ , one can find another Calabi-Yau manifold  $(X^{\vee}, J^{\vee}, \omega^{\mathbb{C}^{\vee}})$  s.t.  $H^q(X, \Omega^pTX) \cong H^q(X^{\vee}, \Omega^p_{X^{\vee}})$  naturally and vice versa, i.e. we get a local isomorphism on the tangent spaces to their corresponding moduli spaces. Additionally, we'd like to say that the superconformal field theories are equivalent (mostly physics-related statement).

This statement is definitely not true in the generality above, and one manifold can have various mirrors.

1.2. **A-model and B-model.** There exist two "topologically twisted" variants of nonlinear sigma models called the A-model and the B-model which have the following nice feature: although the model above depends on both the complex and symplectic (i.e. complexified Kähler) structure, the A-model depends only on  $\omega^{\mathbb{C}}$  while the B-model only depends on J. Mirror symmetry thus says that the A-model on  $(X, \omega^{\mathbb{C}}) \leftrightarrow B$ -model on  $(X^{\vee}, J^{\vee})$  and the B-model on  $(X, J) \leftrightarrow A$ -model on  $(X^{\vee}, \omega^{\mathbb{C}^{\vee}})$ .

To make mathematical sense of this, we would like numerical quantities that define what these models do (note that the A and B-models don't actually correspond to the physical world). We specifically look at "correlation functions", for instance Gromov-Witten invariants.

#### 2. Hodge Theory and Quantum Cohomology

The first feature that we expect is that  $H^q(X, \Omega^p TX) \cong H^q(X^{\vee}, \Omega_{X^{\vee}}^p)$ . In the Calabi-Yau case, the exterior powers  $\bigwedge^p TX$  are naturally isomorphic to  $\Omega^{n-p}$ , so  $v_1 \wedge \cdots \wedge v_p \mapsto i_{v_1} \cdots i_{v_p} \Omega$ . In terms of Dolbeault cohomology,  $H^{n-p,q}(X) \cong H^{p,q}(X^{\vee})$ . This has some odd consequences: for instance,  $H^3(X,\mathbb{C}) = H^{3,0} \oplus H^{2,1} \oplus H^{1,2} \oplus H^{0,3} \cong H^{0,0} \oplus H^{1,1} \oplus H^{2,2} \oplus H^{3,3}$ . One can cook up examples that match these numerically (i.e. by dimension), but we want a stronger duality.

A stronger notion relies on "Yukawa couplings" (which are actually triplings) on  $H^{1,1}$  and  $H^1(X,TX)$ . On  $H^{1,1}(X)$  (i.e. the A-model), we have

$$\langle \omega_1, \omega_2, \omega_3 \rangle = \int_X \omega_1 \wedge \omega_2 \wedge \omega_3 + \sum_{\beta \in H_2(X, \mathbb{Z}), \beta \neq 0} n_\beta \int_\beta \omega_1 \int_\beta \omega_2 \int_\beta \omega_3 \frac{e^{2\pi i \int_\beta \omega^{\mathbb{C}}}}{1 - e^{2\pi i \int_\beta \omega^{\mathbb{C}}}}$$

The latter term will have infinitely many terms, and should converge, but one can think of this as a power series in the final quantity.  $n_{\beta}$  is the "number of genus 0 (rational) complex curves in X representing the class  $\beta$ ". It is not clear why this should be a number, and what specific kinds of curves we actually want to count: the values here emerge from Gromov-Witten theory.

On the other hand, on  $H^1(X, T_X) \cong H^{2,1}(X)$ , we define

(2) 
$$\langle \theta_1, \theta_2, \theta_3 \rangle = \int_X \Omega \wedge (\theta_1 \cdot \theta_2 \cdot \theta_3 \cdot \Omega)$$

where the interior product on the right is

(3) 
$$H^{1}(X, TX)^{\otimes 3} \otimes H^{0}(X, \Omega_{X}^{3}) \to H^{3}(X, \bigwedge^{3} TX \otimes \Omega_{X}^{3}) = H^{0,3}(X)$$

We can also interpret this as derivatives of  $\Omega$  as we change the complex structure (via the Gauss-Manin connection). The claim of mirror symmetric is that, given two mirror manifolds, we have the above isomorphisms and these two couplings are identified with each other.

*Remark.* As stated, this depends on choice of holomorphic volume form, and one could choose any multiple: one thus needs to normalize the volume form.

How do we identify these relations? We hope that we have a relation between  $\omega^{\mathbb{C}}$  on X and  $J^{\vee}$  on  $X^{\vee}$  that exists on the entire moduli space of Calabi-Yau manifolds. That is, this should be induced by a mirror map  $\mathcal{M}_{sympl}(X) \to \mathcal{M}_{cx}(X^{\vee})$  between the moduli spaces of symplectic and complex forms s.t., on tangent spaces, we have the correspondence  $H^{1,1}(X) \cong H^1(X^{\vee}, TX^{\vee})$  under which the above couplings should agree.

The first mathematical prediction was due to Candelas-de la Ossa-Green-Parkes in 1991. For X a quintic 3-fold, i.e. a degree 5 hypersurface in  $\mathbb{CP}^4$  (we do not need to identify a particular one, as the symplectic structure only depends on the volume of  $\mathbb{CP}^4$ ). Since  $H_2(X,\mathbb{Z}) \cong \mathbb{Z}$ , we identify the curves by degree d. For instance,  $n_1 = 2875$  lines on X,  $n_2 = 609250$  conics, and a few higher values were known. CdGP predicted the values  $n_d$  in general (more precisely, they calculated the associated Gromov-Witten invariants, and conjectured that they actually do count rational curves). They did this by computing on  $X^{\vee} = \text{quintic}/(\mathbb{Z}/5)^3$  which is equipped with a one-parameter complex deformation: note that  $h^{2,1}(X^{\vee}) = 1 = h^{1,1}(X), h^{1,1}(X^{\vee}) = 101 = h^{2,1}(X)$ . CdGP defined the mirror map using equations defined by Hodge theory. On the symplectic side, the couplings are fairly easy to compute. Expanding the equation on the complex side and extracting the coefficients of the power series, one obtains the  $n_d$ . We will go over all of this in more detail over the next month.

# 3. Homological Mirror Symmetry (Kontsevich '94)

All the above lies in the world of "closed string theory", i.e. particles are loops and the world sheet is compact. We can instead look at "open string theory", where the worldsheet is a surface with bound and we have constraints on the values of fields at the boundary (called *D*-branes after Dirichlet). Moreover, the axioms of field theory on gluing boundaries should give us a category of

D-branes. On the A-model, the branes are Lagrangian submanifolds with a flat bundle over L, and in the B-model branes are complex analytic submanifolds with a holomorphic vector bundle. Kontsevich came up with a precise mathematical conjecture of what these categories should be.

**Conjecture 2** (Kontsevich's HMS). If  $(X, J, \omega^{\mathbb{C}})$  and  $(X^{\vee}, J^{\vee}, \omega^{\mathbb{C}^{\vee}})$  are mirrors, then

(4) 
$$D^{b}\operatorname{Fuk}(X,\omega^{\mathbb{C}}) \cong D^{b}\operatorname{Coh}(X^{\vee}, J^{\vee})$$
$$D^{b}\operatorname{Coh}(X, J) \cong D^{b}\operatorname{Fuk}(X^{\vee}, w^{\mathbb{C}^{\vee}})$$

as an equivalence of triangulated categories.

Here, the Fukaya category  $\operatorname{Fuk}(X,\omega^{\mathbb{C}})$  is the category whose objects are Lagrangian submanifolds with flat bundle, and the morphisms are given by intersection theory with their compositions given by Floer homology and operations on it. On the other side, we have the category of coherent sheaves  $\operatorname{Coh}(X,J)$ , examples of which are vector bundles on complex submanifolds (which correspond to skyscraper sheaves). The symbol  $D^b$  corresponds to enlarging to the triangulated derived category, i.e. complexes of such objects up to homotopy.

Example. The case  $X = T^2$ /elliptic curve was understood by Polishchuk-Zazlow.

# 4. Strominger-Yau-Zaslow conjecture (1996)

All the above stuff is properties of pairs of manifold that one knows to be mirrors. The SYZ conjecture helps us construct mirror pairs.

Conjecture 3 (SYZ). For  $X, X^{\vee}$  mirrors, they carry mutually dual fibrations by special Lagrangian tori, i.e.

(5) 
$$T^{n} \longrightarrow X , (T^{\vee})^{n} \longrightarrow X^{\vee}$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad B$$

Here,  $L^n \subset X$  is special Lagrangian if  $\omega|_L = 0$  and Im  $\Omega|_L = 0$ , and  $T^{\vee} = \text{Hom}(\pi_1(T), U(1))$ .

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 2

## DENIS AUROUX

Reference for today: M. Gross, D. Huybrechts, D. Joyce, "Calabi-Yau Manifolds and Related Geometries", Chapter 14.

## 1. Deformations of Complex Structures

An (almost) complex structure (X,J) splits the complexified tangent and (wedge powers of) cotangent bundles as

$$TX \otimes \mathbb{C} = TX^{1,0} \oplus TX^{0,1}, v^{0,1} = \frac{1}{2}(v + iJv)$$

$$T^*X \otimes \mathbb{C} = T^*X^{1,0} \oplus T^*X^{0,1}, T^*X^{1,0} = \operatorname{Span}(dz_i), T^*X^{0,1} = \operatorname{Span}(d\overline{z}_i)$$

$$\bigwedge^k T^*X \otimes \mathbb{C} = \bigoplus_{p+q=k} \bigwedge^{p,q} T^*X = \Omega^{p,q}(X)$$

If J is almost complex, these are  $\mathbb{C}$ -vector bundles. J is integrable (i.e. a complex structure)

(2) 
$$[T^{1,0}, T^{1,0}] \subset T^{1,0} \Leftrightarrow d = \partial + \overline{\partial} \text{ maps } \Omega^{p,q} \to \Omega^{p+1,q} \oplus \Omega^{p,q+1} \\ \Leftrightarrow \overline{\partial}^2 = 0 \text{ on diff. forms}$$

We obtain a Dolbeault cohomology for holomorphic vector bundles E:

(3) 
$$C_{\overline{\partial}}^{q}(X,E) = \{ C^{\infty}(X,E) \xrightarrow{\overline{\partial}} \Omega^{0,1}(X,E) \xrightarrow{\overline{\partial}} \Omega^{0,2}(X,E) \to \cdots \}$$
$$H_{\overline{\partial}}^{q}(X,E) = \ker \overline{\partial}/\mathrm{im}\overline{\partial}$$

Deforming J to a "nearby" J' gives

(4) 
$$\Omega_{J'}^{1,0} \subseteq T^* \mathbb{C} = \Omega_J^{1,0} \oplus \Omega_J^{0,1}$$

is a graph of a linear map  $(-s): \Omega_J^{1,0} \to \Omega_J^{0,1}$ . J' is determined by  $\Omega_{J'}^{1,0}$  (acted on by i) and  $\Omega_{J'}^{0,1}$  (acted on by i'). s is a section of  $(\Omega_J^{1,0})^* \otimes \Omega_J^{0,1} = \mathbb{T}_j^{1,0} \otimes \Omega_J^{0,1}$  i.e. a  $(0,1)_J$ -form with values in  $T_J^{1,0}X$ . If  $z_1,\ldots,z_n$  are local holomorphic

coordinates for J, then  $s = \sum s_{ij} \frac{\partial}{\partial z_i} \otimes d\overline{z}_j$ . A basis of (1,0)-forms for J' is given

by 
$$dz_i - \underbrace{\sum_j s_{ij} d\overline{z}_j}_{s(dz_i)}$$
 and  $(0,1)$ -vectors for  $J'$  by  $\frac{\partial}{\partial \overline{z}_k} + \underbrace{\sum_\ell s_{\ell k} \frac{\partial}{\partial z_\ell}}_{s(\partial/\partial \overline{z}_k)}$ .

We can use this to test the integrability of J'. The Dolbeault complex  $(\bigoplus_q \Omega_X^{0,q} \otimes TX^{1,0}, \overline{\partial})$  ( $\overline{\partial}$  acts "on forms") carries a Lie bracket

$$[\alpha \otimes v, \alpha' \otimes v'] = (\alpha \wedge \alpha') \otimes [v, v']$$

giving it the structure of a differential graded Lie algebra

**Proposition 1.** J' is integrable  $\Leftrightarrow \overline{\partial}s + \frac{1}{2}[s,s] = 0$ .

*Proof.* We want to check that the bracket of two 0, 1 tangent vectors is still 0, 1, i.e. that

(6) 
$$[\frac{\partial}{\partial \overline{z}_k} + \sum_{\ell} s_{\ell k} \frac{\partial}{\partial z_{\ell}}, \frac{\partial}{\partial \overline{z}_k} + \sum_{\ell} s_{\ell k} \frac{\partial}{\partial z_{\ell}}] \in TX_{J'}^{0,1}$$

Evaluating this bracket gives

(7) 
$$\sum_{\ell} \left( \frac{\partial s_{\ell j}}{\partial \overline{z}_i} - \frac{\partial s_{\ell i}}{\partial \overline{z}_j} \right) \frac{\partial}{\partial z_{\ell}} + \sum_{k,\ell} \left( s_{ki} \frac{\partial s_{\ell j}}{\partial z_k} - s_{kj} \frac{\partial s_{\ell i}}{\partial z_k} \right) \frac{\partial}{\partial z_{\ell}}$$

We want this to be 0, i.e. for all  $i, j, \ell$ ,

(8) 
$$0 = \underbrace{\frac{\partial s_{\ell j}}{\partial \overline{z}_{i}} - \frac{\partial s_{\ell i}}{\partial \overline{z}_{j}}}_{\text{coefficient of } \frac{\partial}{\partial z_{\ell}} \otimes (d\overline{z}_{i} \wedge d\overline{z}_{j}) \text{ in } (\overline{\partial}s)} + \sum_{k} \underbrace{\left(s_{k i} \frac{\partial s_{\ell j}}{\partial z_{k}} - s_{k j} \frac{\partial s_{\ell i}}{\partial z_{k}}\right)}_{\text{in } \frac{1}{2}[s,s]}$$

We leave the rest as an exercise.

We would now like to use this to understand the moduli space of complex structures. Define

(9) 
$$\mathcal{M}_{CX}(X) = \{ J \text{ integrable complex structures on } X \} / \text{Diff}(X)$$

(or, assuming that  $\operatorname{Aut}(X, J)$  is discrete, we want that near J,  $\exists$  a universal family  $\mathcal{X} \to \mathcal{U} \subset \mathcal{M}_{CX}$  (complex manifolds, holomorphic fibers  $\cong X$ ) s.t. any family of integrable complex structures  $\mathcal{X}' \to S$  induces a map  $S \to \mathcal{U}$  s.t.  $\mathcal{X}$  pulls back to  $\mathcal{X}'$ ). We have an action of the diffeomorphisms of X: for  $\phi \in \operatorname{Diff}(X)$  close to id,

(10) 
$$d\phi: TX \otimes \mathbb{C} \xrightarrow{\sim} \phi^* TX \otimes \mathbb{C}$$
$$\partial \phi: TX^{1,0} \to \phi^* TX^{1,0}$$
$$\overline{\partial} \phi: TX^{0,1} \to \phi^* TX^{1,0}$$

SO

(11) 
$$\phi^* dz_i = dz_i \circ d\phi = dz_i \circ \partial\phi + dz_i \circ \overline{\partial}\phi$$
$$= \underbrace{(dz_i \circ \partial\phi)}_{(1,0) \text{ for } J} (\operatorname{id} + (\partial\phi)^{-1} \cdot \overline{\partial}\phi)$$

Deformation by  $s \in \Omega^{0,1}(X, TX^{1,0})$  gives  $\Omega^{1,0}_{J'} = \{\alpha - s(\alpha) | \alpha \in \Omega^{1,0}\}$  (the graph of -s): taking  $s = -(\partial \phi)^{-1} \cdot \overline{\partial} \phi : TX^{0,1} \to \phi^* TX^{1,0} \to TX^{1,0}$  gives the desired element of  $\Omega^{0,1}(TX^{1,0})$ .

1.1. First-order infinitesimal deformations. Given a family J(t), J(0) = J gives  $s(t) \in \Omega^{0,1}(X, TX^{1,0}), s(0) = 00$ . By the above, this should satisfy

(12) 
$$\overline{\partial}s(t) + \frac{1}{2}[s(t), s(t)] = 0$$

In particular,  $s_1 = \frac{ds}{dt}|_{t=0}$  solves  $\overline{\partial} s_1 = 0$ . We obtain an infinitesimal action of Diff(X): for  $(\phi_t)$ ,  $\phi_0 = \mathrm{id}$ ,  $\frac{d\phi}{dt}|_{t=0} = v$  a vector field,

(13) 
$$\frac{d}{dt}|_{t=0}(-(\partial\phi_t)^{-1}\circ\overline{\partial}\phi_t) = -\frac{d}{dt}|_{t=0}(\overline{\partial}\phi_t) = -\overline{\partial}v$$

This implies that first-order deformations are given as

(14) 
$$\operatorname{Def}_{1}(X, J) = \frac{\operatorname{Ker}(\overline{\partial} : \Omega^{0,1}(TX^{1,0}) \to \Omega^{2,0}(TX^{1,0}))}{\operatorname{Im}(\overline{\partial} : C^{\infty}(TX^{1,0}) \to \Omega^{0,1}(TX^{1,0}))}$$

We can write this more compactly using Dolbeault cohomology, namely  $H^1_{\overline{\partial}}(X, TX^{1,0})$ . Furthermore, given a family

$$(15) \qquad \begin{array}{c} X \longrightarrow \mathcal{X} \\ \downarrow \qquad \qquad \downarrow \\ * \longrightarrow S \end{array}$$

of deformations of (X, J) parameterized by S, we get a map  $T_*S \to H^1(X, TX^{1,0})$  called the *Kodaira Spencer map* 

Remark. A complex manifold (X, J) is a union of complex charts  $U_i$  with biholomorphisms  $\phi_{ij}: U_{ij} \stackrel{\sim}{\to} U_{ji}$  s.t.  $\phi_{ij} = \phi_{ji}^{-1}$  and  $\phi_{ij}\phi_{jk} = \phi_{ik}$  on  $U_{ijk}$ . Deformations of (X, J) come from deforming the gluing maps  $\phi_{ij}$  among the space of holomorphic maps. To first order, this is given by holomorphic vector fields  $v_{ij}$  on  $U_i \cap U_j$  s.t.  $v_{ij} = -v_{ji}$  and  $v_{ij} + v_{jk} = v_{ik}$  on  $U_{ijk}$ . This is precisely the Čech 1-cocycle conditions in the sheaf of holomorphic tangent vector fields. Modding out by holomorphic functions  $\psi_i: U_i \stackrel{\sim}{\to} U_i$  (which act by  $\phi_{ij} \mapsto \psi_j \phi_{ij} \psi_i^{-1}$ ) is precisely modding by the Čech coboundaries. Thus,  $\mathrm{Def}_1(X, J) = \check{H}^1(X, TX^{1,0})$ .

1.2. Obstructions to Deformation. Given a first-order deformation  $s_1$ , one can ask if one can find an actual deformation  $s(t) = s_1 t + O(t^2)$  (or even a formal deformation, i.e. non-convergent power series). Expand

(16) 
$$s(t) = s_1 t + s_2 t^2 + \dots \in \Omega^{0,1}(X, TX^{1,0})$$

Then the condition  $\overline{\partial}s(t) + \frac{1}{2}[s(t), s(t)] = 0$  implies that  $\overline{\partial}s_1 = 0, \overline{\partial}s_2 + \frac{1}{2}[s_1, s_1] = 0, \overline{\partial}s_3 + [s_1, s_2] = 0, \cdots$ . Now, we need  $[s_1, s_1] \in \operatorname{im}(\overline{\partial}) \subset \Omega^{0,2}(TX^{1,0})$ . We know that  $[s_1, s_1] \in \operatorname{Ker}(\overline{\partial})$ . Thus, the primary obstruction to deforming is the class of  $[s_1, s_1]$  in  $H^2(X, TX^{1,0})$ . If it is zero, then there is an  $s_2$  s.t.  $\overline{\partial}s_2 + \frac{1}{2}[s_1, s_1] = 0$ , and the next obstructure is the class of  $[s_1, s_2] \in H^2(X, TX^{1,0})$ . We are basically attempting to apply by brute force the implicit function theorem.

If it happens that  $H^2(X, TX) = 0$ , then the deformations are unobstructed and the moduli space of complex structures is locally a smooth orbifold (not a manifold, because we may have to quotient by automorphisms) with tangent space  $H^1(X, TX^{1,0})$ . For Calabi-Yau manifolds, this will not be true: however, we still have

**Theorem 1** (Bogomolov-Tian-Todorov). For X a compact Calabi-Yau  $(\Omega_X^{n,0} \cong \mathcal{O}_X)$  with  $H^0(X,TX)=0$  (automorphisms are discrete), deformations of X are unobstructed and, assuming  $\operatorname{Aut}(X,J)=\{1\}$ ,  $\mathcal{M}_{CX}$  is locally a smooth manifold with  $T\mathcal{M}_{CX}=H^1(X,TX)$ .

**Theorem 2** (Griffiths Transversality). For a family  $(X, J_t)$ ,  $\alpha_t \in \Omega^{p,q}(X, J_t) \Longrightarrow \frac{d}{dt}|_{t=0}\alpha_t \in \Omega^{p,q} + \Omega^{p+1,q-1} + \Omega^{p-1,q+1}$ .

*Proof.*  $J_t$  is given by  $s(t) \in \Omega^{0,1}(TX^{1,0}), s(0) = 0$ . In local coordinates, we have  $T^*X_{J_t}^{1,0} = \operatorname{Span}\{dz_i^{(t)} = dz_i - \sum s_{ij}(t)d\overline{z}_j\}$ 

(17) 
$$\alpha_t = \sum_{I,J||I|=p,|J|=q} \alpha_{IJ}(t) dz_{i_1}^{(t)} \wedge \dots \wedge dz_{i_p}^{(t)} \wedge d\overline{z}_{j_1}^{(t)} \wedge \dots \wedge d\overline{z}_{j_q}^{(t)}$$

Taking  $\frac{d}{dt}|_{t=0}$ , the result follows from the product rule. We mostly get (p,q) terms and a few (p+1,q-1), (p-1,q+1) forms (the latter from  $\frac{d}{dt}|_{t=0}(dz_{i_k}^{(t)})$ .

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 3

## DENIS AUROUX

Last time, we say that a deformation of (X, J) is given by

(1) 
$$\{s \in \Omega^{0,1}(X, TX) | \overline{\partial}s + \frac{1}{2}[s, s] = 0\} / \text{Diff}(X)$$

To first order, these are determined by  $\operatorname{Def}_1(X,J) = H^1(X,TX)$ , but extending these to higher order is obstructed by elements of  $H^2(X,TX)$ . In the Calabi-Yau case, recall that:

**Theorem 1** (Bogomolov-Tian-Todorov). For X a compact Calabi-Yau  $(\Omega_X^{n,0} \cong \mathcal{O}_X)$  with  $H^0(X,TX)=0$  (automorphisms are discrete), deformations of X are unobstructed.

Note that, if X is a Calabi-Yau manifold, we have a natural isomorphism  $TX \cong \Omega_X^{n-1}, v \mapsto i_v \Omega$ , so

(2) 
$$H^{0}(X, TX) = H^{n-1,0}(X) \cong H^{0,1}$$

and similarly

(3) 
$$H^{1}(X,TX) = H^{n-1,1}, H^{2}(X,TX) = H^{n-1,2}$$

## 1. Hodge theory

Given a Kähler metric, we have a Hodge \* operator and  $L^2$ -adjoints

(4) 
$$d^* = -*d*, \overline{\partial}^* = -*\partial*$$

and Laplacians

(5) 
$$\Delta = dd^* + d^*d, \overline{\square} = \overline{\partial}\overline{\partial}^* + \overline{\partial}^*\overline{\partial}$$

Every  $(d/\overline{\partial})$ -cohomology class contains a unique harmonic form, and one can show that  $\overline{\square} = \frac{1}{2}\Delta$ . We obtain

(6) 
$$H_{dR}^{k}(X,\mathbb{C}) \cong \operatorname{Ker} \left(\Delta : \Omega^{k}(X,\mathbb{C}) \circlearrowleft\right) = \operatorname{Ker} \left(\overline{\square} : \Omega^{k} \circlearrowleft\right)$$
$$\cong \bigoplus_{p+q=k} \operatorname{Ker} \left(\overline{\square} : \Omega^{p,q} \circlearrowleft\right) \cong \bigoplus_{p+q=k} H_{\overline{\partial}}^{p,q}(X)$$

The Hodge \* operator gives an isomorphism  $H^{p,q} \cong H^{n-p,n-q}$ . Complex conjugation gives  $H^{p,q} \cong \overline{H^{q,p}}$ , giving us a *Hodge diamond* 

$$h^{n,n} \qquad h^{n-1,n} \qquad \cdots \qquad h^{0,n}$$

$$h^{n,n-1} \qquad h^{n-1,n-1} \qquad \cdots \qquad \vdots$$

$$\vdots \qquad \vdots \qquad \vdots \qquad \vdots \qquad \vdots$$

$$h^{n,0} \qquad \cdots \qquad h^{1,1} \qquad h^{0,1}$$

For a Calabi-Yau, we have

(8) 
$$H^{p,0} \cong H^{n,n-p} = H^{n-p}_{\overline{\partial}}(X, \Omega_X^n) \cong H^{n-p}_{\overline{\partial}}(X, \mathcal{O}_X) = H^{0,n-p} \cong \overline{H^{n-p,0}}$$

Specifically, for a Calabi-Yau 3-fold with  $h^{1,0}=0$ , we have a reduced Hodge diamond

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

Mirror symmetry says that there is another Calabi-Yau manifold whose Hodge diamond is the mirror image (or 90 degree rotation) of this one.

There is another interpretation of the Kodaira-Spencer map  $H^1(X,TX)\cong H^{n-1,1}$ . For  $\mathcal{X}=(X,J_t)_{t\in S}$  a family of complex deformations of (X,J),  $c_1(K_X)=-c_1(TX)=0$  implies that  $\Omega^n_{(X,J_t)}\cong \mathcal{O}_X$  under the assumption  $H^1(X)=0$ , so we don't have to worry about deforming outside the Calabi-Yau case. Then  $\exists [\Omega_t]\in H^{n,0}_{J_t}(X)\subset H^n(X,\mathbb{C})$ . How does this depend on t? Given  $\frac{\partial}{\partial t}\in T_0S, \frac{\partial t}{\partial \Omega_t}\in \Omega^{n,0}\oplus \Omega^{n-1,1}$  by Griffiths transversality:

(10) 
$$\alpha_t \in \Omega_{J_t}^{p,q} \implies \frac{\partial}{\partial t} \alpha_t \in \Omega^{p,q} + \Omega^{p-1,q+1} + \Omega^{p+1,q-1}$$

Since  $\frac{\partial \Omega_t}{\partial t}|_{t=0}$  is d-closed  $(d\Omega_t = 0)$ ,  $(\frac{\partial \Omega_t}{\partial t}|_{t=0})^{(n-1,1)}$  is  $\overline{\partial}$ -closed, while

(11) 
$$\overline{\partial} (\frac{\partial \Omega_t}{\partial t}|_{t=0})^{(n-1,1)} + \overline{\partial} (\frac{\partial \Omega_t}{\partial t}|_{t=0})^{(n-1,1)} = 0$$

Thus,  $\exists [(\frac{\partial \Omega_t}{\partial t}|_{t=0})^{(n-1,1)}] \in H^{n-1,1}(X)$ .

For fixed  $\Omega_0$ , this is independent of the choice of  $\Omega_t$ . If we rescale  $f(t)\Omega_t$ ,

(12) 
$$\frac{\partial}{\partial t}(f(t)\Omega_t) = \frac{\partial f}{\partial t}\Omega_t + f(t)\frac{\partial \Omega_t}{\partial t}$$

Taking  $t \to 0$ , the former term is (n,0), while for the latter, f(0) scales linearly with  $\Omega^0$ .

(13) 
$$H^{n-1,1}(X) = H^1(X, \Omega_X^{n-1}) \cong H^1(X, TX)$$

and the two maps  $T_0S \to H^{n-1,1}(X)$ ,  $H^1(X,TX)$  agree. Hence, for  $\theta \in H^1(X,TX)$  a first-order deformation of complex structure,  $\theta \cdot \Omega \in H^1(X,\Omega_X^n \otimes TX) = H^{n-1,1}(X)$  and (the Gauss-Manin connection)  $[\nabla_{\theta}\Omega]^{(n-1,1)} \in H^{n-1,1}(X)$  are the same. We can iterate this to the third-order derivative: on a Calabi-Yau three-fold, we have

(14) 
$$\langle \theta_1, \theta_2, \theta_3 \rangle = \int_X \Omega \wedge (\theta_1 \cdot \theta_2 \cdot \theta_3 \cdot \Omega) = \int_X \Omega \wedge (\nabla_{\theta_1} \nabla_{\theta_2} \nabla_{\theta_3} \Omega)$$

where the latter wedge is of a (3,0) and a (0,3) form.

## 2. Pseudoholomorphic curves

(reference: McDuff-Salamon) Let  $(X^{2n}, \omega)$  be a symplectic manifold, J a compatible almost-complex structure,  $\omega(\cdot, J\cdot)$  the associated Riemannian metric. Furthermore, let  $(\Sigma, j)$  be a Riemann surface of genus  $g, z_1, \ldots, z_k \in \Sigma$  market points. There is a well-defined moduli space  $\mathcal{M}_{g,k} = \{(\Sigma, j, z_1, \ldots, z_k)\}$  modulo biholomorphisms of complex dimension 3g - 3 + k (note that  $\mathcal{M}_{0,3} = \{\text{pt}\}$ ).

**Definition 1.**  $u: \Sigma \to X$  is a J-holomorphic map if  $J \circ du = du \circ J$ , i.e.  $\overline{\partial}_J u = \frac{1}{2}(du + Jduj) = 0$ . For  $\beta \in H_2(X, \mathbb{Z})$ , we obtain an associated moduli space

$$(15) M_{g,k}(X,J,\beta) = \{(\Sigma,j,z_1,\ldots,z_k), u : \Sigma \to X | u_*[\Sigma] = \beta, \overline{\partial}_J u = 0\} / \sim$$

where  $\sim$  is the equivalence given by  $\phi$  below.

(16) 
$$\Sigma, z_1, \dots, z_k \xrightarrow{u} X$$

$$\phi \downarrow \cong$$

This space is the zero set of the section  $\overline{\partial}_J$  of  $\mathcal{E} \to \operatorname{Map}(\Sigma, X)_\beta \times \mathcal{M}_{g,k}$ , where  $\mathcal{E}$  is the (Banach) bundle defined by  $\mathcal{E}_u = W^{r,p}(\Sigma, \Omega^{0,1}_{\Sigma} \otimes u^*TX)$ .

We can define a linearized operator

$$D_{\overline{\partial}}: W^{r+1,p}(\Sigma, u^*TX) \times T\mathcal{M}_{q,k} \to W^{r,p}(\Sigma, \Omega_{\Sigma}^{0,1} \otimes U^*TX)$$

(17) 
$$D_{\overline{\partial}}(v,j') = \frac{1}{2} (\nabla v + J \nabla v j + (\nabla_v J) \cdot du \cdot j + J \cdot du \cdot j')$$
$$= \overline{\partial} v + \frac{1}{2} (\nabla_v J) du \cdot j + \frac{1}{2} J \cdot du \cdot j'$$

This operator is Fredholm, with real index

(18) 
$$\operatorname{index}_{\mathbb{R}} D_{\overline{\partial}} := 2d = 2\langle c_1(TX), \beta \rangle + n(2 - 2g) + (6g - 6 + 2k)$$

One can ask about transversality, i.e. whether we can ensure that  $D_{\bar{\partial}}$  is onto at every solution. We say that u is regular if this is true at u: if so,  $\mathcal{M}_{g,k}(X,J,\beta)$  is smooth of dimension 2d.

**Definition 2.** We say that a map  $\Sigma \to X$  is simple (or "somewhere injective") if  $\exists z \in \Sigma$  s.t.  $du(z) \neq 0$  and  $u^{-1}(u(z)) = \{z\}$ .

Note that otherwise u will factor through a covering  $\Sigma \to \Sigma'$ . We set  $\mathcal{M}_{g,k}^*(X,J,\beta)$  to be the moduli space of such simple curves.

**Theorem 2.** Let  $\mathcal{J}(X,\omega)$  be the set of compatible almost-complex structures on X: then

(19)

 $\mathcal{J}^{reg}(X,\beta) = \{J \in \mathcal{J}(X,\omega) | \text{ every simple } J\text{-holomorphic curve in class } \beta \text{ is regular} \}$  is a Baire subset in  $\mathcal{J}(X,\omega)$ , and for  $J \in \mathcal{J}^{reg}(X,\beta)$ ,  $\mathcal{M}_{g,k}^*(X,J,\beta)$  is smooth (as an orbifold, if  $\mathcal{M}_{g,k}$  is an orbifold) of real dimension 2d and carries a natural orientation.

The main idea here is to view  $\overline{\partial}_J u = 0$  as an equation on  $\operatorname{Map}(\Sigma, X) \times \mathcal{M}_{g,k} \times \mathcal{J}(X,\omega) \ni (u,j,J)$ . Then  $D_{\overline{\partial}}$  is easily seen to be surjective for simple maps. We have a "universal moduli space"  $\tilde{MM}^* \stackrel{\pi_J}{\to} \mathcal{J}(X,\omega)$  given by a Fredholm map, and by Sard-Smale, a generic J is a regular value of  $\pi_J$ . This universal moduli space is  $\mathcal{M}^* = \bigsqcup_{J \in \mathcal{J}(X,\omega)} \mathcal{M}^*_{g,k}(X,J,\beta)$ . For such J,  $\mathcal{M}^*_{g,k}(X,J,\beta)$  is smooth of dimension 2d, and the tangent space is  $\operatorname{Ker}(D_{\overline{\partial}})$ . For the orientability, we need an orientation on  $\operatorname{Ker}(D_{\overline{\partial}})$ . If J is integrable, the  $D_{\overline{\partial}}$  is  $\mathbb{C}$ -linear  $(D_{\overline{\partial}} = \overline{\partial})$ , so  $\operatorname{Ker}$  is a  $\mathbb{C}$ -vector space. Moreover,  $\forall J_0, J_1 \in \mathcal{J}^{reg}(X,\beta)$ ,  $\exists$  a (dense set of choices of) path  $\{J_t\}_{t\in[0,1]}$  s.t.  $\bigsqcup_{t\in[0,1]} \mathcal{M}^*_{g,k}(X,J_t,\beta)$  is a smooth oriented cobordism. We still need compactness.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 4

## DENIS AUROUX

## 1. Pseudoholomorphic Curves

For  $(X^{2n}, \omega)$  symplectic, J a compatible a.c.s.  $\in \mathcal{J}(X, \omega)$ ,

(1) 
$$\mathcal{M}_{g,k} = \{(\Sigma, j) \text{ genus } g, z_1, \dots, z_k \in \Sigma \text{ marked points}\}$$

**Definition 1.**  $u: \Sigma \to X$  is J-holomorphic if  $\overline{\partial}_J u = \frac{1}{2}(du + Jdu \cdot j) = 0$ , and for  $\beta \in H_2(X, \mathbb{Z})$ , we have a moduli space

(2) 
$$\mathcal{M}_{g,k}(X,J,\beta) = \{(\Sigma,j,z_1,\ldots,z_k), u|u_*[\Sigma] = \beta, \overline{\partial}_J u = 0\}/\sim$$

 $u:\Sigma\to X$  is simple if it doesn't factor  $\Sigma\to\Sigma'\to X$ . We can define a linearized operator

(3) 
$$D_{\overline{\partial}}: W^{r+1,p}(\Sigma, u^*TX) \times T\mathcal{M}_{g,k} \to W^{r,p}(\Sigma, \Omega_{\Sigma}^{0,1} \otimes U^*TX)$$
$$D_{\overline{\partial}}(v, j') = \overline{\partial}v + \frac{1}{2}(\nabla_v J)du \cdot j + \frac{1}{2}J \cdot du \cdot j'$$

This operator is Fredholm, with real index

(4) 
$$\operatorname{index}_{\mathbb{R}} D_{\overline{\partial}} := 2d = 2\langle c_1(TX), \beta \rangle + n(2-2g) + (6g-6+2k)$$
  
 $u$  is regular if  $D_{\overline{\partial}}$  is onto.

**Theorem 1.** The set  $\mathcal{J}^{reg}(X,\beta)$  of  $J \in \mathcal{J}(X,\omega)$  s.t. every simple J-holomorphic curve in class  $\beta$  is regular is a Baire subset. For  $J \in \mathcal{J}^{reg}(X,\beta)$ , the subset of simple maps  $\mathcal{M}_{g,k}^*(X,J,\beta) \subset \mathcal{M}_{g,k}(X,J,\beta)$  is smooth and oriented of dimension 2d.

Let  $g(\cdot, \cdot) = \omega(\cdot, J \cdot)$  be the associated Riemannian metric.

**Theorem 2** (Gromov Compactness). If  $u_n : \Sigma_n \to X$  is a sequence of J-holomorphic curves,  $J \in \mathcal{J}(X,\omega)$ ,  $E(u_n) = \int_{\Sigma_n} u_n^* \omega = \langle [\omega], u_{n*}[\Sigma_n] \rangle$  bounded  $\leq E_0 < \infty$ , then  $\exists$  a subsequence which converges to a stable map  $u_\infty : \Sigma_\infty \to X$ .

Here  $\Sigma_{\infty}$  is a union of nodal Riemann surfaces.

Remark. The phenomenon occurring here (besides the degeneration of  $\Sigma_n$  comes from the bubbling of spheres. For instance, for  $u_n: S^2 = \mathbb{CP}^1 = \mathbb{C} \cup \infty \to \mathbb{CP}^1 \times \mathbb{CP}^1$ ,  $(x_0: x_1) \mapsto (x_0: x_1)$ ,  $(nx_1: x_0)$ , we see that, in the affine chart

 $x = x_1/x_0$ ,  $\mathbb{C}^* \to \mathbb{C}^2$ ,  $x \mapsto x$ ,  $\frac{1}{nx}$  which extends at  $0, \infty$  to  $\mathbb{CP}^1 \times \mathbb{CP}^1$ . Away from x = 0, it converges uniformly to  $x \mapsto (x, 0)$ . But if you reparameterize to  $\tilde{x} = nx$ ,  $\tilde{x} \mapsto (\frac{1}{n}\tilde{x}, \frac{1}{\tilde{x}})$  and away from  $x = \infty$ , it converges uniformly to  $\tilde{x} \to (0, \frac{1}{\tilde{x}})$ .

The general idea is:

- Identify bubbling regions where sup  $|du_n| \to \infty$ .
- Away from those,  $\exists$  convergent subsequences.
- Near them, we can rescale the doim to  $v_n(z) = u_n(z_n^0 + \epsilon_n z), \epsilon_n \to 0$  so  $\sup |dv_n|$  does not tend to  $\infty$  and there is a subsequence converging to  $v_{\infty}$ .
- The process is finite because  $\forall u$  nonconstant holomorphic curves (closed domain).

(5) 
$$E(u) = \int |du|^2 = \int u^* \omega \ge \hbar > 0$$

Assuming we can achieve transversality for all stable J-holomorphic curves in the class  $\beta$ , then

(6)  $\overline{\mathcal{M}}_{g,k}(X,J,\beta) = \{ (\text{nodal}) \text{ } J\text{-holomorphic curves of genus } g \text{ representing } \beta \} / \sim$  is compact and oriented of real dimension  $2d = 2\langle c_1(TX), \beta \rangle + 2(n-3)(1-g) + 2k$  with a fundamental class

$$[\overline{M}_{q,k}(X,J,\beta)] \in H_{2d}(\overline{M}_{q,k}(X,J,\beta),\mathbb{Q})$$

This moduli space is equipped with evaluation maps  $\operatorname{ev}_i: \overline{\mathcal{M}}_{g,k}(X,J,\beta) \to X, (\Sigma,j,z_1,\ldots,z_k,u) \mapsto u(z_i)$  for  $1 \leq i \leq k$ . The Gromov-Witten invariants are defined as follows: given  $\alpha_1,\ldots,\alpha_k \in H^*(X), \sum \operatorname{deg}(\alpha_i) = 2d$ ,

(8) 
$$\langle \alpha_1, \dots, \alpha_k \rangle_{g,\beta} = \int_{[\overline{M}_{g,k}(X,J,\beta)]} \operatorname{ev}_1^* \alpha_1 \wedge \dots \wedge \operatorname{ev}_k^* \alpha_k \in \mathbb{Q}$$

Equivalently, if we represent  $PD(\alpha_i)$  by a cycle  $C_i \subset X$  (choose  $C_i$  transverse to the evaluation map), then the pairing is simply  $\#([\overline{M}_{g,k}(X,J,\beta)] \cap \bigcap_i \operatorname{ev}_i^{-1}(C_i))$  (or rather  $\#(\operatorname{ev}_*[\overline{M}_{g,k}(X,J,\beta)] \cap (C_1 \times \cdots \times C_k))$  in  $X^k$ , where  $\operatorname{ev} = (\operatorname{ev}_1, \ldots, \operatorname{ev}_n)$ ). That is, we are asking how many curves in the homology class  $\beta$  pass through the cycles  $C_i$ . Note that, for a Calabi-Yau 3-fold, 2d = 2k, so regular curves are isolated:  $\#[\overline{M}_{g,0}(X,J,\beta)] \in \mathbb{Q}$ .

1.1. More on the case of Calabi-Yau 3-folds, g = 0. For the symplectic geometer, note that we have transversality for simple curves, by taking J generic. However, multiple covers  $\Sigma' \xrightarrow{d\cdot 1} \Sigma \xrightarrow{\beta} X$  always occur with excess dimension  $\forall J$ . Also, these have automorphisms (deck transformations of the covering). Thus,  $\mathcal{M}_{0,k}(X,J,d\beta)$  are orbifolds (strata of multiply-covered maps are orbifolded). We can restore transversality by taking domain-dependent Js. More precisely, there

is a universal curve  $\mathcal{C} \to \overline{\mathcal{M}}_{0,k}$  (the fiber over a point is the corresponding curve), and J is now given by a map  $\mathcal{C} \to \mathcal{J}(X,\omega)$ . The holomorphic curve equation becomes  $u: (\Sigma, j) \to X, du + J(u(z), z)du \cdot j = 0$ . We choose a superposition of a finite number perturbations, which break the symmetry of the multiple covers and give us transversality.

In order to obtain compactness, we need to include stable maps (i.e. chains of nodal Riemann surfaces). If we have transversality, these have real codimension  $\geq 2$  in  $\overline{\mathcal{M}}_{g,k}(X,J,\beta)$ , i.e.  $\mathcal{M}_{0,k}(X,J,\beta)$  defines a pseudocycle, so we can still define the fundamental class. The point is that, in a Calabi-Yau 3-fold, for a generic J, we get transversality for all simple curves. Given  $\beta \in H_2(X,\mathbb{Z})$ ,  $\exists$  finitely many classes  $\beta_i$  with  $E(\beta_1) \leq \cdots \leq E(\beta_n) = \beta$  containing J-holomorphic curves. The simple curves are isolated, and for a generic J, the simple curves are disjoint. So in a stable map  $\Sigma_{\infty} \to X$ , all nonconstant components have the same image, so we treat this as a multiple cover.

For an algebraic geometer, one needs to keep J integrable so X remains an algebraic variety. The moduli space  $\overline{\mathcal{M}}_{g,k}$  is an algebraic stack, as is  $\overline{\mathcal{M}}_{g,k}(X,J,\beta)$ . For an integrable J and fixed j, we have a  $\overline{\partial}$ -operator on sections of  $u^*TX$ , and the cokernel of this operator is precisely  $H^1(\Sigma, u^*TX)$ . Where  $du \neq 0$ , we have  $u^*TX = T\Sigma \oplus u^*N$  and  $H^1(\Sigma, T\Sigma)$  is simply the deformations of j. There is also an obstruction bundle  $\underline{\mathrm{Obs}}_u = H^1(\Sigma, u^*N_\Sigma)$  if u is an immersion. We claim that we can define an obstruction sheaf  $\underline{\mathrm{Obs}} \to \overline{\mathcal{M}}_{g,k}(X,J,\beta)$ , and perturbing our equation to  $\overline{\partial}_J u = \nu$  yields a section  $\pi_{\mathrm{Coker}}(\nu)$  of  $\underline{\mathrm{Obs}}$ . We can obtain a "virtual" fundamental class  $[\overline{\mathcal{M}}_{g,k}(X,J,\beta)]^{virt} \in H_{2d}(\overline{\mathcal{M}}_{g,k}(X,J,\beta),\mathbb{Q})$ , and if  $\underline{\mathrm{Obs}}$  is a bundle, this virtual fundamental class is Poincaré dual to Euler class of the obstruction bundle.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 5

## DENIS AUROUX

## 1. Gromov-Witten Invariants

Recall that if  $(X, \underline{\omega})$  is a symplectic manifold, J an almost-complex structure,  $\beta \in H_2(X, \mathbb{Z})$ ,  $\overline{\mathcal{M}}_{g,k}(X, J, \beta)$  is the set of (possibly nodal) J-holomorphic maps to X of genus g representing class  $\beta$  with k marked points up to equivalence. This is not a nice moduli space, but does have a fundamental class  $[\overline{\mathcal{M}}_{g,k}(X,J,\beta)] \in H_{2d}(\overline{\mathcal{M}}_{g,k}(X,J,\beta),\mathbb{Q})$ , where  $2d = \langle c_1(TX),\beta \rangle + 2(n-3)(1-g)+2k$ . We further have an evaluation map  $\mathrm{ev} = (\mathrm{ev}_1,\ldots,\mathrm{ev}_n): \overline{\mathcal{M}}_{g,k}(X,J,\beta) \to X^k, (\Sigma,z_1,\ldots,z_k,u) \mapsto (u(z_1),\ldots,u(z_k))$ . Then the Gromov-Witten invariants are defined for  $\alpha_1,\ldots,\alpha_k \in H^*(X), \sum \deg \alpha_i = 2d$  by

(1) 
$$\langle \alpha_1, \dots, \alpha_k \rangle_{g,\beta} = \int_{[\overline{M}_{g,k}(X,J,\beta)]} \operatorname{ev}_1^* \alpha_1 \wedge \dots \wedge \operatorname{ev}_k^* \alpha_k \in \mathbb{Q}$$

Or dually, for  $\alpha_i = PD(C_i)$ ,  $\#(\text{ev}_*[\overline{M}_{g,k}(X,J,\beta)] \cap (C_1 \times \cdots \times C_k)) \in \mathbb{Q}$ . For a Calabi-Yau 3-fold, we're interested in g = 0, k = 3, so  $\Sigma = (S^2, \{0, 1, \infty\})$ . For deg  $\alpha_i = 2, \alpha_i = PD(C_i)$ ,  $C_i$  cycles transverse to the evaluation map, we have

(2) 
$$\langle \alpha_1, \alpha_2, \alpha_3 \rangle_{0,\beta} = \#\{u : S^2 \to X \text{ } J\text{-hol. of class } \beta, \\ u(0) \in C_1, u(1) \in C_2, u(\infty) \in C_3\} / \sim$$

Reparameterization acts transitively on triples of points, so

(3)  

$$\langle \alpha_1, \alpha_2, \alpha_3 \rangle_{0,\beta} = (C_1 \cdot \beta)(C_2 \cdot \beta)(C_3 \cdot \beta) \#\{u : S^2 \to X \text{ } J\text{-hol. of class } \beta\} / \sim$$

$$= (\int_{\beta} \alpha_1)(\int_{\beta} \alpha_2)(\int_{\beta} \alpha_3) \cdot \#[\overline{\mathcal{M}}_{0,0}(X, J, \beta)]$$

We denote by  $N_{\beta} \in \mathbb{Q}$  the latter number  $\#[\overline{\mathcal{M}}_{0,0}(X,J,\beta)]$ . This works when  $\beta \neq 0$ : when  $\beta = 0$ , we instead obtain

(4) 
$$\langle \alpha_1, \alpha_2, \alpha_3 \rangle_{0,0} = \int_X \alpha_1 \wedge \alpha_2 \wedge \alpha_3$$

1.1. Yukawa coupling. Physicists write this as

(5) 
$$\langle \alpha_1, \alpha_2, \alpha_3 \rangle = \int_X \alpha_1 \wedge \alpha_2 \wedge \alpha_3 + \sum_{0 \neq \beta \in H_2(X, \mathbb{Z})} \langle \alpha_1, \alpha_2, \alpha_3 \rangle_{0,\beta} e^{2\pi i \int_\beta B + i\omega}$$

We want to ignore issues of convergence, and so treat this is a formal power series

(6) 
$$\langle \alpha_1, \alpha_2, \alpha_3 \rangle = \int_X \alpha_1 \wedge \alpha_2 \wedge \alpha_3 + \sum_{\beta \neq 0} \langle \alpha_1, \alpha_2, \alpha_3 \rangle_{0,\beta} q^{\beta} \in \Lambda$$

where  $\Lambda$  is the completion of the group ring  $\mathbb{Q}[H_2(X,\mathbb{Z})] = \{\sum a_i q^{\beta_i} | a_i \in \mathbb{Q}, \beta_i \in H_2\}$ . Specifically, we allow infinite sums provided that  $\int_{\beta_i} \omega \to +\infty$ .

1.2. Quantum cohomology. This is new product structure on  $H^*(X)$  deformed by this coupling. Namely, pick a basis  $(\eta_i)$  of  $H^*(X)$ ,  $(\eta^i)$  the dual basis, i.e.  $\int_X \eta_i \wedge \eta^j = \delta_{ij}$ . Set

(7) 
$$a_1 * a_2 = \sum_{i} \langle \alpha_1, \alpha_2, \eta^i \rangle \eta_i = \alpha_1 \wedge \alpha_2 + \sum_{\beta \neq 0} \langle \alpha_1, \alpha_2, \eta^i \rangle_{0,\beta} q^\beta \eta_i$$

**Definition 1.** The quantum cohomology of X is  $QH^*(X) = (H^*(X;\Lambda),*)$ .

**Theorem 1.** This is an associative algebra.

The proof of this relies on understanding the relationship between 4 point GW invariants and various 3 point ones.

1.3. **Kähler moduli.** We can view q as the coordinates on a Kähler moduli space: for (X, J)-complex, the Kähler cone  $\mathcal{K}(X, J) = \{[\omega] | \omega \text{ Kahler}\} \subset H^{1,1}(X) \cap H^2(X, \mathbb{R}) \text{ is a open, convex cone. Its real dimension is } h^{1,1}(X), \text{ and we can make it a complex manifold by adding the "B-field".$ 

**Definition 2.** Let (X, J) be a Calabi-Yau 3-fold with  $h^{1,0} = 0$  (so  $h^{2,0} = 0$  and  $H^{1,1} = H^2$ ). Then the complexified Kähler moduli space is

(8) 
$$\mathcal{M}_{Kah} = (H^2(X, \mathbb{R}) + i\mathcal{K}(X, J))/H^2(X, \mathbb{Z})$$
$$= \{ [B + i\omega], \omega \ Kahler \}/H^2(X, \mathbb{Z})$$

Choose a basis  $(e_i)$  of  $H^2(X,\mathbb{Z})$ ,  $e_1,\ldots,e_m \in \overline{\mathcal{K}(X,J)}$  (which exists by openness). We can write  $[B+i\omega] = \sum t_i e_i, t_i \in \mathbb{C}/\mathbb{Z}$ , so we have coordinates on  $\mathcal{M}_{Kah}$  given by  $q_i = \exp(2\pi i t_i)$ . Thus,  $\mathcal{M}_{Kah}$  is an open subset of  $(\mathbb{C}^*)^m$  which contains  $(\mathbb{D}^*)^m$ , where  $\mathbb{D}^* = \{q | 0 < |q| < 1\}$ .

We now can associate  $q^{\beta}$  to  $q_1^{d_1} \cdots q_m^{d_m}$ , where  $d_i = \int_{\beta} e_i$  for  $e_i \geq 0$  integers (it is an integer cohomology class integrated against an integer homology class): explicitly,  $q_1^{d_1} \cdots q_m^{d_m} = \exp(2\pi i \sum d_i t_i) = \exp(2\pi i \int_{\beta} B + i\omega)$ . We can view  $\langle \alpha_1, \alpha_2, \alpha_3 \rangle$  as a power series in the  $q_i$ , though we still do not know about convergence.

1.4. Gromov-Witten invariants vs. numbers of curves. We have, for  $\alpha_1, \alpha_2, \alpha_3 \in H^2(X)$ ,

(9) 
$$\langle \alpha_1, \alpha_2, \alpha_3 \rangle = \int_X \alpha_1 \wedge \alpha_2 \wedge \alpha_3 + \sum_{\beta \neq 0} \langle \alpha_1, \alpha_2, \alpha_3 \rangle_{0,\beta} q^{\beta}$$
$$= \int_X \alpha_1 \wedge \alpha_2 \wedge \alpha_3 + \sum_{\beta \neq 0} (\int_\beta \alpha_1) (\int_\beta \alpha_2) (\int_\beta \alpha_3) N_\beta q^{\beta}$$

This is much like our formula from the first class, except the latter term had the form  $n_{\beta} \frac{q^{\beta}}{1-q^{\beta}}$  and  $n_{\beta}$  as the number of "rational curves of class  $\beta$ ". The discrepancy comes from the existence of multiple covers. Let  $C \subset X$  be an embedded rational curve in a Calabi-Yau 3-fold. A theorem of Grothendieck says that a holomorphic bundle over  $\mathbb{P}^1$  splits as  $\bigoplus \mathcal{O}_{\mathbb{P}^1}(d_i)$ , where  $\mathcal{O}(d)$  is the sheaf whose sections are homogeneous degree d holomorphic functions on  $\mathbb{C}^2$  and  $\mathcal{O}(-1)$  is the tautological bundle. Writing  $NC \cong \mathcal{O}_{\mathbb{P}^1}(d_1) \oplus \mathcal{O}_{\mathbb{P}^1}(d_2)$ , we obtain

(10) 
$$0 = c_1(TX)[C] = c_1(NC)[C] + c_1(TC)[C] = d_1 + d_2 + 2$$

so  $d_1 + d_2 = -2$ . The "generic case" is  $d_1 = d_2 = -1$ , in which case C is automatically regular as a J-holomorphic curve. The contribution of C to the Gromov-Witten invariant  $N_{[C]}$  is precisely 1. On the other hand, there is a component  $\mathcal{M}(kC) \subset \mathcal{M}_{0,0}(X, J, k[C])$  consisting of k-fold covers of C. What is  $\#[\mathcal{M}(kC)]$ ?

**Theorem 2.** If  $NC \cong \mathcal{O}(-1) \oplus \mathcal{O}(-1)$ , then the contribution of C to  $N_{k[C]}$  is  $\frac{1}{k^3}$ .

There are various proofs, all of which are somewhat difficult. For instance, Voisin shows that  $\exists$  perturbed  $\overline{\partial}$ -equations  $\overline{\partial}_J u = \nu(z, u(z))$  s.t. the moduli space  $\tilde{M}M_3(kC)$  (of perturbed J-holomorphic maps with 3 marked points representing k[C] and whose image lies in a neighborhood of C) is smooth and has real dimension 6. Moreover,  $(\mathrm{ev}_1 \times \mathrm{ev}_2 \times \mathrm{ev}_3)_* [\tilde{\mathcal{M}}_3(kC)] = [C \times C \times C] \in H_6(X \times X \times X)$ . Then the contribution of C to  $\langle \alpha_1, \alpha_2, \alpha_3 \rangle_{0,k[C]}$  is

(11) 
$$\int_{ev_*[\tilde{\mathcal{M}}_3]} \alpha_1 \times \alpha_2 \times \alpha_3 = \left(\int_C \alpha_1\right) \left(\int_C \alpha_2\right) \left(\int_C \alpha_3\right) = \frac{1}{k^3} \left(\int_{kC} \alpha_1\right) \left(\int_{kC} \alpha_2\right) \left(\int_{kC} \alpha_3\right)$$

We expect that (\*)  $N_{\beta} = \sum_{\beta=k\gamma} \frac{1}{k^3} n_{\gamma}$ .

Remark. We do not know if  $n_{\gamma}$  is what we think it is, but we use this formula as a definition; see the Gopakumar-Vafa conjecture, which claims that  $n_{\gamma} \in \mathbb{Z}$ , and the theory of Donaldson-Thomas invariants and MNOP conjectures.

Assuming (\*), we have

(12) 
$$\sum_{\beta} (\int_{\beta} \alpha_{1}) (\int_{\beta} \alpha_{2}) (\int_{\beta} \alpha_{3}) N_{\beta} q^{\beta} = \sum_{k,\gamma} (\int_{k\gamma} \alpha_{1}) (\int_{k\gamma} \alpha_{2}) (\int_{k\gamma} \alpha_{3}) \frac{n_{\gamma}}{k^{3}} q^{k\gamma}$$
$$= \sum_{\gamma} (\int_{\gamma} \alpha_{1}) (\int_{\gamma} \alpha_{2}) (\int_{\gamma} \alpha_{3}) n_{\gamma} \sum_{k \geq 1} k^{k\gamma}$$

Where we are headed: we correspond this pairing to

(13) 
$$\langle \theta_1, \theta_2, \theta_3 \rangle = \int_X \Omega \wedge (\nabla_{\theta_1} \nabla_{\theta_2} \nabla_{\theta_3} \Omega)$$
 on  $H^{2,1}(\check{X})$ .

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 6

## DENIS AUROUX

## 1. The Quintic 3-fold and Its Mirror

The simplest Calabi-Yau's are hypersurfaces in toric varieties, especially smooth hypersurfaces X in  $\mathbb{CP}^{n+1}$  defined by a polynomial of degree d=n+2, i.e. a section of  $\mathcal{O}_{\mathbb{P}^{n+1}}(d)$ . Smoothness implies that  $NX \stackrel{\sim}{\to} \mathcal{O}_{\mathbb{P}^{n+1}}(d)|_X$ , defined by  $v \mapsto \nabla_v P = dP(v)$ , so  $T\mathbb{P}^{n+1}|_X = TX \oplus NX = TX \oplus \mathcal{O}_{\mathbb{P}^{n+1}}(d)|_X$  ("adjunction"). Passing to the dual and taking the determinant, we obtain

$$(1) \qquad \qquad \Omega^{n+1}|_{\mathbb{P}^{n+1}}|_X \cong \Omega^n_X \otimes \mathcal{O}_{\mathbb{P}^{n+1}}(-d)|_X$$

Now:

(2)

$$T_{\ell}\mathbb{P}^{n+1} \oplus \mathbb{C} = \operatorname{Hom}(\ell, \ell^{\perp}) \oplus \operatorname{Hom}(\ell, \ell) = \operatorname{Hom}(\ell, \mathbb{C}^{n+2}) = \operatorname{Hom}(\mathcal{O}(-1)_{\ell}, \mathbb{C}^{n+2})$$

implying that  $T\mathbb{P}^{n+1} \oplus \mathcal{O} \cong \mathcal{O}(1)^{n+2}$ . Again, passing to the dual and taking the determinant, we obtain

(3) 
$$\Omega_{\mathbb{P}^{n+1}}^{n+1} \otimes \mathcal{O} \cong \mathcal{O}(-1)^{\otimes (n+2)} = \mathcal{O}(-(n+2))$$

We finally have

$$(4) \mathcal{O}_{\mathbb{P}^{n+1}}(-(n+2))|_{X} \cong \Omega_{X}^{n} \otimes \mathcal{O}_{\mathbb{P}^{n+1}}(-d)|_{X} \implies \Omega_{X}^{n} \cong \mathcal{O}$$

if d = n + 2, i.e. our X is indeed Calabi-Yau.

*Example.* Cubic curves in  $\mathbb{P}^2$  correspond to elliptic curves (genus 1, isomorphic to tori), while quartic surfaces in  $\mathbb{P}^3$  are K3 surfaces.

The quintic in  $\mathbb{P}^4$  is the world's most studied Calabi-Yau 3-fold. The cohomology of the quintic can be computed via the Lefschetz hyperplane theorem: inclusion induces  $i_*: H_r(X) \xrightarrow{\sim} H_r(\mathbb{CP}^4)$  for r < n = 3, so  $H_1(X) = 0$ ,  $H_2(X) = H_2(\mathbb{CP}^4) = \mathbb{Z}$ . Thus,  $h^{1,0} = 0$  and  $h^{2,0} = 0$ : by argument seen before,  $h^{1,1} = 1$ . Moreover,

(5) 
$$\chi(X) = e(TX) \cdot [X] = c_3(TX) \cdot [X]$$

By working out  $c(T\mathbb{P}^4)|_X = c(TX)c(\mathcal{O}_{\mathbb{P}^4}(5))|_X$  (from adjunction), we have

(6) 
$$c(T\mathbb{P}^4) = c(T\mathbb{P}^4 \oplus \mathcal{O}) = c(\mathcal{O}(1)^{\oplus 5}) = (1+h)^5$$

where  $h = c_1(\mathcal{O}(1))$  is the generator of  $H_2(\mathbb{CP}^4)$  and is Poincaré dual to the hyperplane. Restricting to X gives

(7) 
$$(1+h|_X)^5 = 1+5h|_X+10h^2|_X+10h^3|_X = (1+c_1+c_2+c_3)(1+5h|_X)$$
  
so  $c_1 = 0$ ,  $c_2 = 10h^2|_X$ ,  $c_3 = -40h^3|_X$ . Thus,

(8) 
$$\chi(X) = -40h^3 \cdot [X] = -40([line] \cap [X]) = -40 \cdot 5 = -200$$

We conclude that

(9) 
$$h_0 + h_2 - h_3 + h_4 + h_6 = 1 + 1 - \dim H_3(X) + 1 + 1 = -200$$

implying that dim  $H_3=204$ . Since  $h^{3,0}=h^{0,3}=1$ , we obtain  $h^{1,2}=h^{2,1}=101$ . In fact,  $h^{1,1}=1$ , and we have a symplectic parameter given by the area of a generator of  $H_2(X)$  (given by the class of a line in  $H_2(\mathbb{P}^4)$ ). We further have  $101=h^{2,1}$  complex parameters: the equation of the quintic gives  $h^0(\mathcal{O}_{\mathbb{P}^4}(5))=\binom{9}{5}=126$  dimensions, from which we lose one by passing to projective space, and 24 by modding out by  $\operatorname{Aut}(\mathbb{CP}^4)=PGL(5,\mathbb{C})$ . That is, all complex deformations are still quintics.

Now we construct the mirror of X. Start with a distinguished family of quintic 3-folds

(10) 
$$X_{\psi} = \{(x_0 : \dots : x_4) \in \mathbb{P}^4 \mid f_{\psi} = x_0^5 + \dots + x_4^5 - 5\psi x_0 x_1 x_2 x_3 x_4 = 0\}$$

Let  $G = \{(a_0, \ldots, a_4) \in (\mathbb{Z}/5\mathbb{Z})^5 \mid \sum a_i = 0\}/(\mathbb{Z}/5\mathbb{Z}) = \{(a, a, a, a, a)\}$ . Then  $G \cong (\mathbb{Z}/5\mathbb{Z})^3$  acts on  $X_{\psi}$  by  $(x_j) \mapsto (x_j \xi^{a_j})$  where  $\xi = e^{2\pi i/5}$  ( $f_{\psi}$  is G-invariant because  $\sum a_j = 0 \mod 5$ , and (1, 1, 1, 1, 1) acts trivially because the  $x_j$  are homogeneous coordinates). Furthermore,  $X_{\psi}$  is smooth for  $\psi$  generic (i.e.  $\psi^5 \neq 1$ ), but  $X_{\psi}/G$  is singular: the action has fixed point  $(x_0 : \cdots : x_4) \in X_{\psi}$  s.t. at least two coordinates are 0. This consists of

- 10 curves  $C_{ij}$ , where e.g.  $C_{01} = \{x_0 = x_1 = 0, x_2^5 + x_3^5 + x_4^5 = 0\}$  with stabilizer  $\mathbb{Z}/5 = \{(a, -a, 0, 0, 0)\}$ , so  $C_{01}/G \cong \mathbb{P}^1$  is the line  $y_2 + y_3 + y_4 = 0$  in  $\mathbb{P}^2$ ,  $y_i = x_i^5$ , and
- 10 points  $P_{ijk}$ , e.g.  $P_{0,1,2} = \{x_0 = x_1 = x_2 = 0, x_3^5 + x_4^5 = 0\}$  with stabilizer  $(\mathbb{Z}/5\mathbb{Z})^2$ , so  $P_{012}/G = \{\text{pt}\}$ .

The singular locus of  $X_{\psi}/G$  is the 10 curves  $\overline{C_{ij}} = C_{ij}/G \cong \mathbb{P}^1$  with  $\overline{C}_{ij}, \overline{C}_{jk}, \overline{C}_{ik}$  meeting at the point  $\overline{P}_{ijk}$ .

Next, let  $X_{\psi}^{\vee}$  be the resolution of singularities of  $(X_{\psi}/G)$ , i.e.  $X_{\psi}^{\vee}$  smooth and equipped with a map  $X_{\psi}^{\vee} \xrightarrow{\pi} X_{\psi}/G$  which is an isomorphism outside  $\pi^{-1}(\bigcup C_{ij})$ . The explicit construction is complicated, and one can use toric geometry to do it. One can further show that it is a crepant resolution, i.e. the canonical bundle  $K_{X_{\psi}^{\vee}} = \pi^* K_{X_{\psi}/G}$ , so the Calabi-Yau condition is preserved and  $X_{\psi}^{\vee}$  is a Calabi-Yau 3-fold.

Along  $\overline{C}_{ij}$  (away from  $\overline{P}_{ijk}$ ),  $X_{\psi}/G$  looks like  $(\mathbb{C}^2/(\mathbb{Z}/5\mathbb{Z})) \times \mathbb{C}$ ,  $(x_1, x_1, x_3) \sim (\xi^a x_i, \xi^{-a} x_2, x_3)$ . Now  $\mathbb{C}^2/(\mathbb{Z}/5\mathbb{Z}) \cong \{uv = w^5\} \subset \mathbb{C}^3$ ,  $[x_1, x_2] \mapsto [x_1^5, x_2^5, x_1 x_2]$  is an  $A_4$  singularity, which can be resolved by blowing up twice, getting four exceptional divisors. Doing this for each  $\overline{C}_{ij}$  gives 40 divisors. Similarly, resolving each  $\overline{p}_{ijk}$  creates six divisors, for a total of 60 divisors. Thus,  $X_{\psi}^{\vee}$  contains 100 new divisors in addition to the hyperplane section, so indeed  $h^{1,1}(X_{\psi}^{\vee}) = 101$ . Similarly, as we were only able to build a one-parameter family,  $h^{2,1}(X_{\psi}^{\vee}) = 1$ , giving us mirror symmetric Hodge diamonds:

$$(11) h^{ij}(X) = \begin{pmatrix} 1 & 0 & 0 & 1 \\ 0 & 1 & 101 & 0 \\ 0 & 101 & 1 & 0 \\ 1 & 0 & 0 & 1 \end{pmatrix}, h^{ij}(X_{\psi}^{\vee}) = \begin{pmatrix} 1 & 0 & 0 & 1 \\ 0 & 101 & 1 & 0 \\ 0 & 1 & 101 & 0 \\ 1 & 0 & 0 & 1 \end{pmatrix}$$

We want to see how mirror symmetry predicts the Gromov-Witten invariants  $N_d$  (the "number of rational curves"  $n_d$ ) of the quintic. For that, we need to understand the mirror map between the Kähler parameter  $q = \exp(2\pi i \int_{\ell} B + i\omega)$  on X and the complex parameter  $\psi$  on the mirror  $X_{\psi}^{\vee}$  (which will also give, by differentiating, an isomorphism  $H^{1,1}(X) \xrightarrow{\sim} H^{2,1}(X)$ ) as well as calculations of the Yukawa coupling on  $H^{2,1}(X_{\psi}^{\vee})$ .

- 1.1. **Degenerations and the Mirror Map.** Last time, we saw a basis  $\{e_i\}$  of  $H^2(X,\mathbb{Z})$  by elements of the Kähler cone gives coordinates on the complexified Kähler moduli space: if  $[B+i\omega] = \sum t_i e_i$ , the parameter  $q_i = \exp(2\pi i t_i) \in \mathbb{C}^*$  gives the large volume limit as  $q_i \to 0$ , Im  $(t_i) \to \infty$ . Physics predicts that the mirror situation is degeneration of a large complex structure limit and that, near such a limit point, there are "canonical coordinates" on the complex moduli spaces making it possible to describe the mirror map.
  - Degeneration: consider a family  $\mathcal{X} \xrightarrow{\pi} D^2$  where for  $t \neq 0, X_t \cong X$  (with varying J) and for t = 0,  $X_0$  is typically singular. For instance, consider the camily of elliptic curves  $C_t = \{y^2z = x^3 + x^2z tz^3\} \subset \mathbb{CP}^2$  (in affine coordinates,  $C_t : y^2 = x^3 + x^2 t$ ).  $C_t$  is a smooth torus for  $t \neq 0$ , and nodal at t = 0, obtained by pinching a loop on the torus.
  - Monodromy: follow the family  $(X_t)$  as t varies along the loop in  $\pi_1(D^2 \setminus \{0\}, t_0)$  going around the origin. All the  $X_i$ s are diffeomorphic, and thus induce a monodromy diffeomorphism  $\phi$  of  $X_{t_0}$ , defined up to isotopy. This in turn induces  $\phi_* \in \operatorname{Aut}(H_n(X_{t_0}, \mathbb{Z}))$ . In the above example,  $\phi$  acts on  $H_1(C_{t_0}) = \mathbb{Z}^2$  by  $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$  (the Dehn twist): observe that  $C_t \stackrel{2:1}{\to} \mathbb{CP}^1 = \mathbb{C} \cup \{\infty\}$  by projection to x, and the branch points are  $\infty$  plus the roots of  $x^3 + x^2 t$ . As  $t \to 0$ , there is one root near -1 and two near 0, which rotate as t goes around 0. Letting a be the line between the two roots

near 0 and b be between the root near -1 and the closest other root, the monodromy maps a, b to a, b + a.

Remark. Note that this complex parameter t is ad hoc. A more natural way to describe the degeneration would be to describe  $C_t$  as an abstract elliptic curve  $C_t \cong \mathbb{C}/\mathbb{Z} + \tau(t)\mathbb{Z}$ . Then  $\tau(t)$ , or rather  $\exp(2\pi i\tau)$ , is a better quantity. Equip  $C_t$  with a holomorphic volume form  $\Omega_t$  normalized so  $\int_a \Omega_t = 1 \,\forall t$ . Then let  $\tau(t) = \int_b \Omega_t$ : as t goes around the origin,  $\tau(t) \to \tau(t) + 1$  since  $b \mapsto b + a$ . Moreover,  $q(t) = \exp(2\pi i\tau(t))$  is still single-valued, and as  $t \to 0$ , we still have  $\operatorname{Im} \tau(t) \to \infty$  and  $q(t) \to 0$ . In the former case, we have  $\int_a \frac{dx}{y} \in -i\mathbb{R}^+$  tending to 0 and  $\int_b \frac{dx}{y} \in \mathbb{R}^+$  tending to a constant value, so the ratio goes to  $+i\infty$ . In the latter case, q(t) is a holomorphic function of t, and goes around 0 once when t does, i.e. it has a single root at t = 0. Thus, q is a local coordinate for the family.

Next time, we will see an analogue of this for a family of Calabi-Yau manifolds.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 7

## DENIS AUROUX

## 1. Degenerations and Monodromy (contd.)

Last time, we considered families  $\mathcal{X} \xrightarrow{\pi} D^2$  where for  $t \neq 0, X_t \cong X$  (with varying J) and for t = 0,  $X_0$  is typically singular. We saw that monodromy around t = 0 induces  $\phi_* \in \operatorname{Aut}(H^n(X_{t_0}, \mathbb{Z}))$ .

**Theorem 1.** All eigenvalues of  $\phi_*$  are roots of unity: thus  $\exists N, k$  s.t.  $(\phi_*^N - \text{id})^k = 0$ . Moreover,  $k \leq n + 1$ .

Replacing  $\phi$  by  $\phi^N$  (the "base change"  $X'_t = X_{t^N}$ ), we can assume that  $\phi_*$  is unipotent, i.e.  $(\phi_* - \mathrm{id})^k = 0$ . It is maximally unipotent if k = n + 1. We can further define a weight filtration associated to a unipotent  $\phi_*$  coming from the Jordan block decomposition of  $\phi_*$ : letting

(1) 
$$N = \log(\phi_*) = (\phi_* - \mathrm{id}) - \frac{(\phi_* - \mathrm{id})^2}{2} + \dots + (-1)^{n+1} \frac{(\phi_* - \mathrm{id})^n}{n}$$

act on  $V = H^n(X, \mathbb{Q})$ , we obtain a filtration  $0 \subseteq W_0 \subseteq \cdots \subseteq W_{2n} = V$  s.t.  $N(W_i) \subset W_{i-2}$  and  $N^k : W_{n+k}/W_{n+k-1} \xrightarrow{\sim} W_{n-k}/W_{n-k-1}$ . We construct this as follows:

- First,  $N^n: W_{2n}/W_{2n-1} \xrightarrow{\sim} W_0$  so  $W_0 = \operatorname{im}(N^n), W_{2n-1} = \operatorname{Ker}(N^n)$ .
- Then let  $V' = W_{2n-1}/W_0$ , so N induces  $N' \in \text{End}(V')$  (since  $W_{2n-1} = \text{Ker } N^n \supseteq \text{im } N$  and  $W_0 = \text{im } (N^n) \subseteq \text{Ker } N$ ) with  $(N')^n = 0$ . By induction, we obtain

(2) 
$$0 \subseteq W'_0 \cong W_1/W_0 \subseteq \dots \subseteq W'_{2n-2} \cong W_{2n-1}/W_0 = V'$$
 and

(3) 
$$W_{2n-2} = \{v \mid N^{n-1}(v) \in W_0 = \text{im } N^n\} \supseteq \text{im } N$$
 so  $W_{2n} \stackrel{N}{\to} W_{2n-2}$ . Finally,  $W_1 = \{N^{n-1}(v) \mid N^n(v) = 0\} \subset \text{Ker } N$  so  $W_1 \stackrel{N}{\to} 0$ , and we obtain  $W_k \to W_{k-2}$  by induction.

Example. For the elliptic curves from last time, with  $\phi = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix} = \exp \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ , we have  $0 \subseteq W_0 \subseteq W_1 \subseteq W_2 = H^1(C, \mathbb{Q}) \cong \mathbb{Q}^2$ , with  $W_0 = W_1 = \operatorname{im} N = \operatorname{Ker} N = \operatorname{Span}(a)$  being the direction invariant by monodromy.

Note that if N is the  $(n+1) \times (n+1)$  Jordan block with 0's on the diagonal and 1s above (with columns  $e_i$ ), then  $W_0 = \operatorname{Span}(e_1), W_{2n-1} = \operatorname{Span}(e_1 \cdots e_n)$ , and we can reduce to the equivalent  $(n-1) \times (n-1)$  Jordan block and repeat the process with  $W_1 = W_0, W_{2n-2} = W_{2n-1}, \cdots, W_{2k-2} = W_{2k-1} = \operatorname{Span}(e_1 \cdots e_k)$ . There is a similar story if N is a sum of such Jordan blocks.

Remark. In fact, the interplay of weight filtration with Hodge filtration

$$(4) F^p = H^{n,0} \oplus \cdots \oplus H^{p,n-p} (H^n = F^0 \supseteq F^1 \supseteq \cdots, F^p/F^{p+1} \cong H^{p,n-p})$$

(with Griffiths transversality giving  $\nabla F^p \subseteq F^{p-1}$  under deformations) gives a notion of "mixed Hodge structure". By [Schmid], there exists a limiting Hodge filtration as  $t \to 0$ , but we won't say any more about those.

Now consider a multidimensional family  $\mathcal{X} \to (D^2)^s$  smooth over  $(D^*)^S$  where  $D^* = D^2 \setminus \{0\}$ . Then we have s monodromies  $\phi_1, \ldots, \phi_s \in \operatorname{Aut} H_n(X)$ ,  $[\phi_i, \phi_j] = 0$  (since  $\pi_1((D^*)^s) = \mathbb{Z}^s$  is abelian), so  $N_i = \log \phi_i$  also commute.

**Theorem 2** (Cattani-Kaplan). All the elements of the form  $\sum \lambda_i N_i, \lambda_i > 0$  have the same monodromy weight filtration.

We want to consider a "universal family" of Calabi-Yau manifolds near a "deepest corner", caled a "large complex structure limit point" in the moduli space.

**Definition 1** (Morrison). Given a family of Calabi-Yau n-folds  $\mathcal{X} \to (D^*)^S \subset (D^2)^s$ ,  $s = h^{n-1,1}(X)$ , s.t. the Kodaira-Spencer map  $T_*(D^*)^s \to H^1(TX_t)$  is an isomorphism at every point of  $(D^*)^s$ , we say that  $0 \in (D^2)^s$  is a large complex structure limit (LCSL) point if

- (1) The monodromies  $\phi_j$  around each factor are all unipotent.
- (2) Let  $N_j = \log \phi_j$ ,  $N = \sum \lambda_j N_j$  for  $\lambda_j > 0$  arbitrary. Then the weight filtration  $0 \subseteq W_0 \subseteq W_1 \subseteq \cdots \subseteq W_{2n} = H^n(X, \mathbb{Q})$  has dim  $W_0 = \dim W_1 = 1$ , dim  $W_2 = \dim W_3 = s + 1$ .
- (3) Let  $\alpha_0^*$  be the generator of  $W_0$ ,  $\alpha_1^*$ ,  $\cdots$ ,  $\alpha_s^*$  the rest of a basis for  $W_2$ . Then  $\exists m_{jk} \in \mathbb{Q}$  s.t.  $N_j(\alpha_k^*) = m_{jk}\alpha_0^*$ , i.e.  $\phi_j(\alpha_k^*) = \alpha_k^* + m_{jk}\alpha_0^*$ . We further require that  $(m_{jk})$  is an invertible matrix.

This essentially says that the family is locally a "full deformation", that we single out a one-dimensional subspace  $\mathrm{Span}(\alpha_0^{\vee})$  of  $H^n(X)$  preserved by the monodromy, and that, for each factor  $D^2$ , we get a class  $\tilde{\alpha}_j^*$  s.t.  $\phi_j(\tilde{\alpha}_j^*) = \tilde{\alpha}_j^* + \alpha_0^*$  and  $\tilde{\alpha}_j^*$  is invariant under the other  $\phi_i$ .

Remark. If  $h^{n-1,1} = s = 1$ , then this is equivalent to the statement that the monodromy around zero is maximally unipotent. For instance, the family of elliptic curves seen last time is an LCSL point.

Now, for a family of Calabi-Yau 3-folds, we have by definition

$$(5) \qquad 0 \subset \underbrace{W_0 = W_1}_{\dim = 1} \subset \underbrace{W_2 = W_3}_{\dim = s+1 = h^{2,1}+1} \subset \underbrace{W_4 = W_5}_{\dim = 2s+1} \subset \underbrace{W_6 = H^3(X; \mathbb{Q})}_{\dim = 2s+2}$$

where we use  $N^k: W_{n+k}/W_{n+k-1} \xrightarrow{\sim} W_{n-k}/W_{n-k-1}$  to get the dimensions of  $W_3, W_4, W_5$ . Now,  $H^3(X)$  carries an intersection pairing preserved by  $\phi_*$ , so  $N = \log \phi_*$  is in the Lie algebra, i.e. (x, Ny) + (Nx, y) = 0.

Lemma 1.  $W_{4-2i} = W_{2i}^{\perp}$ .

Proof. Since  $W_0 = \operatorname{im} N^3$ ,  $W_4 = W_5 = \operatorname{Ker} N^3$ ,  $(x, N^3y) = -(N^3x, y) = 0$  for  $x \in W_4$ ,  $N^3y \in W_0$  and the dimensions match. Furthermore,  $N(W_4) = W_2$  (it is onto since  $N: W_4/W_3 \stackrel{\sim}{\to} W_2/W_1$  and  $W_0 = \operatorname{im} N^3 = N(\operatorname{im} N^2)$ ): thus, for  $x, Ny \in W_2$ , (x, Ny) = -(Nx, y) = 0 (since  $W_0 \perp W_4$ ) and the dimensions match.

Finally, passing to  $H_3(X, \mathbb{Q})$  by Poincaré duality, let  $S_i = PD(W_i)$  (or equivalently, viewing  $H_3 = (H^3)^*$ ,  $S_i$  is the annihilator of  $W_{4-2i}$ ).

**Proposition 1.** Given an LCSL point in the moduli space of Calabi-Yau 3 folds with  $h^{2,1} = s$ ,  $\exists a \mathbb{Z}$ -basis  $(\alpha_0, \ldots, \alpha_S, \beta_0, \ldots, \beta_S)$  of  $H_3(X, \mathbb{Z})$  s.t.  $\beta_0 \in S_0$ ,  $\beta_1, \ldots, \beta_s \in S_2$ ,  $\alpha_1, \ldots, \alpha_s \in S_4, \alpha_0 \in S_6 = H_3(X)$  s.t.  $(\alpha_i, \alpha_j) = (\beta_i, \beta_j) = 0$ ,  $(\alpha_i, \beta_j) = \delta_{ij}$ .

Proof. Let  $\beta_0$  be the  $\mathbb{Z}$  generator of  $S_0$  (unique up to sign), which we extend to a  $\mathbb{Z}$ -basis  $\beta_i$  of  $S_2$ . By the lemma,  $S_2$  is Lagrangian w.r.t. the intersection product, so  $(\beta_i, \beta_j) = 0$ . Let  $\beta_i^*$  be the dual basis of  $S_2^* = H^3/W_2$ , i.e.  $\beta_i^*\beta_j = \delta_{ij}$ , and let  $\alpha_i \in H_3$  be the Poincaré dual of some lift of  $\beta_i^*$  to  $H^3$ . Then  $(\alpha_i, \beta_j) = \delta_{ij}$ . We can make  $(\alpha_i, \alpha_j) = 0$  inductively by replacing  $\alpha_i$  with  $\alpha_i - \sum (\alpha_i, \alpha_j)\beta_j$ . Finally,  $\alpha_1, \ldots, \alpha_s \in S_4$  since  $(\alpha_i, \beta_0) = 0$  and  $S_4 = S_0^{\perp}$ .

We now define canonical coordinates on our moduli space. Given  $\mathcal{X} \to (D^*)^s$  LCSL, let  $\Omega(t_1, \ldots, t_s)$  be the holomorphic volume form on  $X_{(t_1, \ldots, t_s)}$ , normalized so that  $\int_{\beta_0} \Omega(t_1, \ldots, t_s) = 1$ . Set  $w_i(t_1, \ldots, t_s) = \int_{\beta_i} \Omega(t_1, \ldots, t_s)$ . This is not quite a coordinate because of monodromy: as  $t_j$  goes around the origin,  $\beta_i \mapsto \phi_j(\beta_i) = \beta_i - m_{ji}\beta_0$  for some  $m_{ji} \in \mathbb{Z}$  (an integer since these are integer classes). In fact, these are the  $m_{ji}$  from the definition of LCSL. Instead, we set  $q_i = \exp(2\pi i w_i)$ : these are well-defined functions on  $(D^*)^s$ , and are canonical once the basis  $\{\beta_i\}$  is chosen. Note that  $q_i$  is a zero of order  $-m_{ji}$  (i.e. a pole of order  $m_{ji}$ ) along  $t_j = 0$ ; if the  $m_{ji}$ 's are nonpositive, then we get coordinates on  $(D^2)^s$ , and can choose a basis of  $S_2$  appropriately.

Example. For our elliptic curves from last time,  $q = \exp(2\pi i \tau(t)), \tau(t) = \int_b \Omega$  where  $\int_a \Omega = 1$ .

If  $e_i$  is a basis of  $H^2(\check{X}, \mathbb{Z})$ ,  $e_i$  in the Kähler cone, we obtain coordinates on the complexified Kähler moduli space: if  $[B+i\omega]=\sum \check{t}_i e_i$ , let  $\check{q}_i=\exp(2\pi i\check{t}_i)$ ,  $\check{t}_i=\int_{e_i^*}B+i\omega$ .

Example. In example above, we have  $\check{q} = \exp(2\pi i \int_{T^2} B + i\omega)$ .

Conjecture 1 (Mirror Symmetry). Let  $f: \mathcal{X} \to (D^*)^S$  be a family of Calabi-Yau 3-folds with LCSL at 0. Then  $\exists$  a Calabi-Yau 3-fold  $\check{X}$  and choices of bases  $\alpha_0, \ldots, \alpha_S, \beta_0, \ldots, \beta_S$  of  $H_3(X, \mathbb{Z}), e_1, \ldots, e_S$  of  $H^2(X, \mathbb{Z})$  s.t. under the map  $m: (D^*)^S \to \mathcal{M}_{Kah}(\check{X}), (q_1, \ldots, q_S) \mapsto (\check{q}_i, \ldots, \check{q}_S), \check{q}_i = q_i$ , we have a coincidence of Yukawa couplings

(6) 
$$\langle \frac{\partial}{\partial q_i}, \frac{\partial}{\partial q_j}, \frac{\partial}{\partial q_k} \rangle_p^X = \langle \frac{\partial}{\partial \check{q}_i}, \frac{\partial}{\partial \check{q}_j}, \frac{\partial}{\partial \check{q}_k} \rangle_{m(p)}^{\check{X}}$$

where the LHS corresponds to  $\int_X \Omega \wedge \left(\frac{\partial}{\partial q_i} \frac{\partial}{\partial q_j} \frac{\partial}{\partial q_k} \Omega\right)$  and the RHS to a (1,1)-coupling, i.e. the Gromov-Witten invariants  $\langle e_i, e_j, e_k \rangle_{0,\beta}^{\check{X}}$  (since  $2\pi i \check{q}_i \frac{\partial}{\partial \check{q}_i} = \frac{\partial}{\partial \check{t}_i} = e_i \in H^{1,1}$ ).

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 8

## DENIS AUROUX

Last time: 18.06 Linear Algebra.

Today: 18.02 Multivariable Calculus. / 18.04 Complex Variables

Thursday: 18.03 Differential Equations

## 1. Mirror Symmetry Conjecture

Last time, we said that if we have a large complex structure limit (LCSL) degeneration, then we have a special basis  $(\alpha_0, \ldots, \alpha_S, \beta_0, \ldots, \beta_S)$  of  $H_3(X, \mathbb{Z})$  s.t.  $\beta_0$  is invariant under monodromy and  $\beta_1, \ldots, \beta_s$  are mapped by monodromy by  $\beta_i \stackrel{\phi_j}{\to} \beta_i - m_{ji}\beta_0$  for  $m_{ji} \in \mathbb{Z}$ . We decided that we would normalize so that  $\int_{\beta_0} \Omega = 1$ , and let  $w_i = \int_{\beta_i} \Omega$   $(w_i \stackrel{\phi_j}{\to} w_i - m_{ji})$  and  $q_i = \exp(2\pi i w_i)$  (which we called canonical coordinates).

Example. Given a family of tori  $T^2$  with monodromy  $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ ,  $\int_a \Omega = 1$ ,  $\int_b \Omega = \tau$  (precisely what you get identifying the elliptic curve with  $\mathbb{R}^2/\mathbb{Z} \oplus \tau\mathbb{Z}$ ),  $q = \exp(2\pi i\tau)$ .

If  $e_i$  is a basis of  $H^2(\check{X}, \mathbb{Z})$ ,  $e_i$  in the Kähler cone, we obtain coordinates on the complexified Kähler moduli space: if  $[B+i\omega]=\sum \check{t}_i e_i$ , let  $\check{q}_i=\exp(2\pi i\check{t}_i)$ ,  $\check{t}_i=\int_{e_i^*}B+i\omega$ .

Example. Returning to our example,  $\check{q} = \exp(2\pi i \int_{T^2} B + i\omega)$ .

Conjecture 1 (Mirror Symmetry). Let  $f: \mathcal{X} \to (D^*)^S$  be a family of Calabi-Yau 3-folds with LCSL at 0. Then  $\exists$  a Calabi-Yau 3-fold  $\check{X}$  and choices of bases  $\alpha_0, \ldots, \alpha_S, \beta_0, \ldots, \beta_S$  of  $H_3(X, \mathbb{Z}), e_1, \ldots, e_S$  of  $H^2(X, \mathbb{Z})$  s.t. under the map  $m: (D^*)^S \to \mathcal{M}_{Kah}(\check{X}), (q_1, \ldots, q_S) \mapsto (\check{q}_i, \ldots, \check{q}_S), \check{q}_i = q_i$ , we have a coincidence of Yukawa couplings

(1) 
$$\langle \frac{\partial}{\partial q_i}, \frac{\partial}{\partial q_j}, \frac{\partial}{\partial q_k} \rangle_p^X = \langle \frac{\partial}{\partial \check{q}_i}, \frac{\partial}{\partial \check{q}_j}, \frac{\partial}{\partial \check{q}_k} \rangle_{m(p)}^{\check{X}}$$

where the LHS corresponds to  $\int_X \Omega \wedge (\frac{\partial}{\partial q_i} \frac{\partial}{\partial q_j} \frac{\partial}{\partial q_k} \Omega)$  and the RHS to a (1,1)coupling, i.e. the Gromov-Witten invariants  $\langle e_i, e_j, e_k \rangle_{0,\beta}^{\check{X}}$  (since  $2\pi i \check{q}_i \frac{\partial}{\partial \check{q}_i} = \frac{\partial}{\partial \check{t}_i} = e_i \in H^{1,1}$  etc.).

Remark. A more grown-up version of mirror symmetry would give you an equivalence between  $H^*(X, \bigwedge TX)$  with its usual product structure and  $H^*(\check{X}, \mathbb{C})$  with the quantum twisted product structure as Frobenius algebras (making this concrete would require more work).

## 1.1. Application to the Quintic (See Gross-Huybrechts-Joyce, after Candelas-de la Ossa-Greene-Parkes). Last time, we defined

(2) 
$$X_{\psi} = \{ (x_0 : \dots : x_4) \in \mathbb{P}^4 \mid f_{\psi} = \sum_{i=0}^4 x_i^5 - 5\psi x_0 x_1 x_2 x_3 x_4 = 0 \}$$

with

(3) 
$$G = \{(a_0, \dots, a_4) \in (\mathbb{Z}/5\mathbb{Z})^5 \mid \sum a_i = 0\}/\{(a, a, a, a, a)\} \cong (\mathbb{Z}/5\mathbb{Z})^3$$

acting by diagonal multiplication  $x_i \mapsto x_i \xi^{a_i}, \xi = e^{2\pi i/5}$ . We obtained a crepant resolution  $\check{X}_{\psi}$  of  $X_{\psi}/G$  (its singularities are  $\overline{C}_{ij} = \{x_i = x_j = 0\}/G$ ), which has  $h^{1,1} = 101$ ,  $h^{2,1} = 1$ , and  $h^3 = 4$ . The map  $(x_0 : \ldots : x_4) \mapsto (\xi^a x_0 : x_1 : \ldots : x_4)$  gives  $X_{\psi} \cong X_{\xi\phi}$ , so let  $z = (5\xi)^{-5}$ . Then  $z \to 0$ , i.e.  $\psi \to \infty$ , gives a toric degeneration of  $X_{\psi}$  to  $\{x_0x_1x_2x_3x_4 = 0\}$ . This is maximally unipotent, as the monodromy on  $H^3$  is given by

$$\begin{pmatrix}
1 & 1 & 0 & 0 \\
0 & 1 & 1 & 0 \\
0 & 0 & 1 & 1 \\
0 & 0 & 0 & 1
\end{pmatrix}$$

so it is LCSL. We want to compute the *periods* of the holomorphic volume form on  $\check{X}_{\psi}$ . There is a volume form  $\check{\Omega}_{\psi}$  on  $\check{X}_{\psi}$  induced by the G-invariant volume form  $\Omega_{\psi}$  on  $X_{\psi}$  by pullback via  $\pi: \check{X}_{\psi} \to X_{\psi}/G$ . We want to find a 3-cycle  $\beta_0 \in H_3(\check{X}_{\psi})$  that survives the degeneration. For z = 0,  $\{\prod x_i = 0\}$  contains tori in component  $\mathbb{P}^3$ 's, e.g.

(5) 
$$T_0 = \{(x_0 : \dots : x_4) \mid x_4 = 1, |x_0| = |x_1| = |x_2| = \delta, x_3 = 0\}$$

We want to extend it to  $z \neq 0$ . Take  $x_4 = 1, |x_0| = |x_1| = |x_2| = \delta$ : then  $x_3$  should be given by the root of  $f_{\psi}$  which tends to 0 as  $\psi \to \infty$ . We need to show that there is only one such value (giving us a simple degeneration rather than a branched covering). Explicitly, set  $x_3 = (\psi x_0 x_1 x_2)^{1/4} y$ :

(6) 
$$f_{\psi} = 0 \Leftrightarrow x_0^5 + x_1^5 + x_2^5 + (\psi x_0 x_1 x_2)^{5/4} y^5 + 1 - 5(\psi x_0 x_1 x_2)^{5/4} y$$

i.e.

(7) 
$$y = \frac{y^5}{5} + \frac{x_0^5 + x_1^5 + x_2^5 + 1}{5(\psi x_0 x_1 x_2)^{5/4}}$$

One root is  $y \sim \psi^{-5/4} \to 0$ , with the other four roots converging to  $\sqrt[4]{5}$ . So for  $x_3$ , we have one root  $\sim \psi^{-1}$ , and 4 roots  $\sim \psi^{1/4}$ . Now, G acts freely on  $T_0 \subset X_{\psi}$ , and  $T_0/G$  is contained in the smooth part of  $X_{\psi}/G$  and gives a torus  $\check{T}_0 \subset \check{X}_{\psi}, \beta_0 = [\check{T}_0]$ . Because  $T_0, \check{T}_0$  still make sense at z = 0, their class is preserved by the monodromy.

Next, we want to get the required holomorphic volume form. In the affine subset  $x_4 = 1$ , let  $\Omega_{\psi}$  be the 3-form on  $X_{\psi}$  characterized uniquely by

(8) 
$$\Omega_{\psi} \wedge df_{\psi} = 5\psi dx_0 \wedge dx_1 \wedge dx_2 \wedge dx_3$$

at each point of  $X_{\psi}$ . At a point where  $\frac{\partial f_{\psi}}{\partial x_3} \neq 0$ ,  $(x_0, x_1, x_2)$  are local coordinates, and

(9) 
$$\Omega_{\psi} = \frac{5\psi dx_0 \wedge dx_1 \wedge dx_2}{\frac{\partial f_{\psi}}{\partial x_2}} = \frac{5\psi dx_0 \wedge dx_1 \wedge dx_2}{5x_3^4 - 5\psi x_0 x_1 x_2}$$

Defining it in terms of other coordinates, we get the same formula on restrictions. We need to extend this to where  $x_4=0$ . We could rewrite this using homogeneous coordinates, but note that the corresponding divisor is just the canonical divisor: since  $X_{\psi}$  is Calabi-Yau, this divisor has no zeroes or poles at  $x_4=0$ . Since  $\Omega_{\psi}$  is G-invariant, it induces a 3-form on  $(X_{\psi}/G)^{\text{nonsing}}$  and lifts and extends to  $\check{\Omega}_{\psi}$  on  $\check{X}_{\psi}$  with

(10) 
$$\int_{\check{T}_0} \check{\Omega}_{\psi} = \frac{1}{5^3} \int_{T_0} \Omega_{\psi}$$

Tool: we have the residue formula

(11) 
$$\frac{1}{2\pi i} \int_{S^1} f(z) dz = \sum_{z_i \text{ poles of } f \in D^2} \operatorname{res}_f(z_i)$$

So let  $T^4 = \{|x_0| = |x_1| = |x_2| = |x_3| = \delta, x_4 = 1\}$ . Then

(12) 
$$\frac{1}{2\pi i} \int_{T^4} \frac{5\psi dx_0 dx_1 dx_2 dx_3}{f_{\psi}} = \int_{T_{TOT,TO}^3} \left( \frac{1}{2\pi i} \int_{S^1} \frac{5\psi dx_3}{f_{\psi}} \right) dx_0 dx_1 dx_2$$

where  $f_{\psi}$  has a unique pole at  $x_3$ . The residue is precisely  $\frac{5\psi}{(\partial f/\partial x_3)}$ , giving us

(13) 
$$= \int_{T_0} \frac{5\psi}{(\partial f/\partial x_3)} dx_0 dx_1 dx_2 = \int_{T_0} \Omega_{\psi}$$

So

$$\int_{T_0} \Omega_{\psi} = \frac{1}{2\pi i} \int_{T^4} \frac{dx_0 dx_1 dx_2 dx_3}{(5\psi)^{-1} (x_0^5 + x_1^5 + x_2^5 + x_3^5 + 1) - x_0 x_1 x_2 x_3} 
= -\frac{1}{2\pi i} \int_{T^4} \frac{dx_0 dx_1 dx_2 dx_3}{x_0 x_1 x_2 x_3} \left( 1 - (5\psi)^{-1} \frac{x_0^5 + x_1^5 + x_2^5 + x_3^5 + 1}{x_0 x_1 x_2 x_3} \right)^{-1} 
= -\frac{1}{2\pi i} \sum_{n=0}^{\infty} \int_{T^4} \frac{dx_0 dx_1 dx_2 dx_3}{x_0 x_1 x_2 x_3} \cdot \frac{(x_0^5 + x_1^5 + x_2^5 + x_3^5 + 1)^m}{(5\psi)^m (x_0 x_1 x_2 x_3)^m}$$

We want to find the coefficient of 1 in the latter term. We obviously need m = 5n (the numerator only has powers which are a multiple of 5), and want the coefficient of  $x_0^{5n}x_1^{5n}x_2^{5n}x_3^{5n}$  in  $(x_0^5 + x_1^5 + x_2^5 + x_3^5 + 1)^{5n}$ , which is  $\frac{(5n)!}{(n!)^5}$ . We finally obtain

(15) 
$$\int_{T_0} \Omega_{\psi} = -(2\pi i)^3 \sum_{n=0}^{\infty} \frac{(5n)!}{(n!)^5 (5\psi)^{5n}}$$

In terms of  $z=(5\psi)^{-5}$ , the period is proportional to

(16) 
$$\phi_0(z) = \sum_{n=0}^{\infty} \frac{(5n)!}{(n!)^5} z^n$$

Set  $a_n = \frac{(5n)!}{(n!)^5}$ . Then

$$(17) (n+1)^4 a_{n+1} = \frac{(5n+5)!}{(n!)^5(n+1)} = 5(5n+4)(5n+3)(5n+2)(5n+1)a_n$$

Setting  $\Theta = z \frac{d}{dz} : \Theta(\sum c_n z^n) = \sum n c_n z^n$ , giving us the *Picard-Fuchs equation* (18)  $\Theta^4 \phi_0 = 5z(5\Theta + 1)(5\Theta + 2)(5\Theta + 3)(5\Theta + 4)\phi_0$ 

Next time, we will show that there is a unique regular solution, and a unique solution with logarithmic poles to our original problem.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 9

## DENIS AUROUX

## 1. The Quintic (contd.)

To recall where we were, we had

(1) 
$$X_{\psi} = \{ (x_0 : \dots : x_4) \in \mathbb{P}^4 \mid f_{\psi} = \sum_{i=0}^4 x_i^5 - 5\psi x_0 x_1 x_2 x_3 x_4 = 0 \}$$

with

(2) 
$$G = \{(a_0, \dots, a_4) \in (\mathbb{Z}/5\mathbb{Z})^5 \mid \sum a_i = 0\}/\{(a, a, a, a, a)\} \cong (\mathbb{Z}/5\mathbb{Z})^3$$

acting by diagonal multiplication  $x_i \mapsto x_i \xi^{a_i}, \xi = e^{2\pi i/5}$ . We obtained a crepant resolution  $\check{X}_{\psi}$  of  $X_{\psi}/G$ . This family has a LCSL point at  $z = (5\psi)^{-5} \to 0$ . There was a volume form  $\check{\Omega}_{\psi}$  on  $\check{X}_{\psi}$  induced by the G-invariant volume form  $\Omega_{\psi}$  on  $X_{\psi}$  by pullback via  $\pi : \check{X}_{\psi} \to X_{\psi}/G$ . We computed its period on the 3-torus

(3) 
$$T_0 = \{(x_0 : \dots : x_4) \mid x_4 = 1, |x_0| = |x_1| = |x_2| = \delta, |x_3| \ll 1\}$$

(or, on the mirror,  $\check{T}_0 \subset \check{X}_{\psi}$ ) to be

(4) 
$$\int_{T_0} \Omega_{\psi} = -(2\pi i)^3 \sum_{n=0}^{\infty} \frac{(5n)!}{(n!)^5 (5\psi)^{5n}}$$

In terms of  $z = (5\psi)^{-5}$ , the period is proportional to

(5) 
$$\phi_0(z) = \sum_{n=0}^{\infty} \frac{(5n)!}{(n!)^5} z^n$$

Setting  $\Theta = z \frac{d}{dz} : \Theta(\sum c_n z^n) = \sum n c_n z^n$ , we obtained the *Picard-Fuchs equation* 

(6) 
$$\theta^4 \phi_0 = 5z(5\Theta + 1)(5\Theta + 2)(5\Theta + 3)(5\Theta + 4)\phi_0$$

**Proposition 1.** All periods  $\int \check{\Omega}_{\psi}$  satisfy this equation.

Note that all period satisfy some 4th order differential equation:  $H^3(\check{X}_{\psi}, \mathbb{C})$  is 4-dimensional, so  $[\check{\Omega}_{\psi}], \frac{d}{d\psi}[\check{\Omega}_{\psi}], \cdots, \frac{d^4}{d\psi^4}[\check{\Omega}_{\psi}]$  are linearly related. Thus, so are their integrals over any 3-cycle.

*Idea of proof.* We view  $\Omega_{\psi}$  and its derivatives as residues. Let

(7) 
$$\overline{\Omega} = \sum_{i=0}^{4} (-1)^{i} x_{i} dx_{0} \wedge \dots \wedge \widehat{dx}_{i} \wedge \dots \wedge dx_{4}$$

be a form on  $\mathbb{C}^5$ . It is homogeneous of degree 5 (not 0), so we need to multiply by something of degree -5 to get a form on  $\mathbb{P}^4$ . If f, g are homogeneous, deg  $f = \deg g + 5$ ,  $\frac{g\Omega}{f}$  is a meromorphic 4-form on  $\mathbb{P}^4$ . For instance,  $\frac{5\psi\Omega}{f\psi}$  has poles along  $X_{\psi}$ . Now, given a 4-form with poles along some hypersurface X, it has a residue on X which is ideally a 3-form on X, but is at least a class in  $H^3(X,\mathbb{C})$ .

Recall from complex analysis, if  $\phi(z)$  has a pole at 0,  $\operatorname{res}_0(\phi) = \frac{1}{2\pi i} \int_{S^1} \phi(z) dz$ . Now, let's say that we have a 3-cycle C in X: we can associate a "tube" 4-cycle in  $\mathbb{P}^4$  which is the preimage of C in the boundary of a tubular neighborhood of X. Then

(8) 
$$\int_{C} \operatorname{res}_{X} \left( \frac{g\overline{\Omega}}{f} \right) := \frac{1}{2\pi i} \int_{\Gamma} \frac{g\overline{\Omega}}{f}$$

If we only have simple poles along X, we get a 3-form characterized by

(9) 
$$\operatorname{res}_{X}\left(\frac{g\overline{\Omega}}{f}\right) \wedge df = g\overline{\Omega}$$

at any point of X.

Now,  $\Omega_{\psi} = \operatorname{res}_{X_{\psi}} \left( \frac{5\psi \overline{\Omega}}{f_{\psi}} \right)$ , and differentiating k times gives

(10) 
$$\frac{\partial^k}{\partial \psi^k} [\Omega_{\psi}] = \operatorname{res}_{X_{\psi}} \left( \frac{g_k \overline{\Omega}}{f_{\psi}^{k+1}} \right)$$

Thus we can express

(11) 
$$\Theta^{4}[\Omega_{\psi}] = \operatorname{res}_{X_{\psi}} \left( \frac{g_{\Theta} \overline{\Omega}}{f_{\psi}^{5}} \right)$$

for some  $g_{\Theta}$ , and write  $5z(5\Theta+1)\cdots(5\Theta+4)[\Omega_{\psi}]$  in the same form.

We compare the residues of forms with order 5 poles along  $X_{\psi}$  using Griffiths pole order reduction. Assume that  $\phi$  is a 3-form with poles of order  $\ell$  along  $X_{\psi}$ ,

$$(12) \qquad \phi = \frac{1}{f_{\psi}^{\ell}} \sum_{i < j} (-1)^{i+j} (x_i g_j - x_j g_i) dx_0 \wedge \dots \wedge \widehat{dx_i} \wedge \dots \wedge \widehat{dx_j} \wedge \dots \wedge dx_4$$

with deg  $(g_0 \cdots g_4) = 5\ell - 4$ , then

(13) 
$$d\phi = \frac{1}{f_{\psi}^{\ell+1}} \left( \ell \sum_{j} g_{j} \frac{\partial f_{\psi}}{\partial x_{j}} - f_{\psi} \sum_{j} \frac{\partial g_{j}}{\partial x_{j}} \right) \overline{\Omega}$$

In particular, if we have something of the form  $(\sum g_j \frac{\partial f_{\psi}}{\partial x_j}) \frac{\overline{\Omega}}{f_{\psi}^{\ell+1}}$  (the Jacobian ideal is the span of  $\{\frac{\partial f_{\psi}}{\partial x_i}\}$ ), it can be written as something with a lower order pole plus something exact. We obtain our result iteratively, showing in each stage that the top order term belongs to the Jacobian ideal, and reduce to a lower order term. When we get to order 1, we find that the residue is 0.

There is a theory of differential equations with regular singular points, i.e. differential equations of the form

(14) 
$$\Theta^s f + \sum_{j=0}^{s-1} B_j(z) \Theta^j f = 0$$

where  $\Theta = z \frac{d}{dz}$  and  $B_j(z)$  are meromorphic functions which are holomorphic at z = 0. As with solving ordinary differential equations, we reduce to a 1st order system of differential equations  $\Theta w(z) = A(z)w(z)$ , where

$$(15) \quad A(z) = \begin{pmatrix} 0 & 1 & & & \\ & 0 & 1 & & \\ & & \ddots & \ddots & \\ & & & \ddots & \ddots & \\ & & & \ddots & 0 & 1 \\ -B_0(z) & \cdots & \cdots & -B_{s-1}(z) \end{pmatrix}, w(z) = \begin{pmatrix} f(z) & \\ \Theta f(z) & \\ \vdots & \\ \Theta^{s-1} f(z) \end{pmatrix}$$

The fundamental theorem of these differential equations states that there exists a constant  $s \times s$  matrix R and an  $s \times s$  matrix of holomorphic functions S(z) s.t.

(16) 
$$\Phi(z) = S(z) \exp((\log z)R) = S(z)(\mathrm{id} + (\log z)R + \frac{\log^2 z}{2}R^2 + \cdots)$$

is a fundamental system of solutions to  $\Theta w(z) = A(z)w(z)$ , and moreover if A(0) doesn't have distinct eigenvalues differing by an integer, we can take R = A(0). This  $\Phi$  is multivalued, and  $z \mapsto e^{2\pi i}z$  gives  $\Phi(z) \mapsto \Phi(z)e^{2\pi iR}$  (where  $e^{2\pi iR}$  is the monodromy).

In our case,  $\mathcal{D}\phi = \Theta^4\phi - 5z(5\Theta + 1)\cdots(5\Theta + 4)\phi = 0$ , so the coefficient of  $\Theta^4$  is  $1 - 5^5z$ , and the coefficients of  $\Theta^0, \cdots, \Theta^3$  are constant multiples of z. Then

(17) 
$$\Theta^4 \phi - \frac{5z}{1 - 5^5 z} P_3(\Theta) \cdot \phi = 0$$

where  $P_3$  is independent of z. Then

(18) 
$$R = A(0) = \begin{pmatrix} 0 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \\ 0 & 0 & 0 & 0 \end{pmatrix}$$

is nilpotent, and our assumption holds. The corresponding monodromy is

(19) 
$$T = e^{2\pi iR} = \begin{pmatrix} 1 & 2\pi i & \frac{(2\pi i)^2}{2} & \frac{(2\pi i)^3}{6} \\ 0 & 1 & 2\pi i & \frac{(2\pi i)^2}{2} \\ 0 & 0 & 1 & 2\pi i \\ 0 & 0 & 0 & 1 \end{pmatrix}$$

If  $\omega(z) = \int_{\beta} \check{\Omega}_{\psi}$  is a period, then it is a solution of the Picard-Fuchs equation, and thus a linear combination of  $\Phi(z)_{1i}$ 's. There exists a basis  $b_1, \ldots, b_4$  of  $H_3(\check{X}, \mathbb{C})$  s.t.  $\int_{b_i} \check{\Omega}_{\psi} = \Phi(z)_{1i}$ . The monodromy action in this basis is T (T maximally unipotent implies that 0 is LSCL).

1.1. More periods of  $\check{\Omega}_{\psi}$ . The first fundamental solution we obtained is  $\phi_0 = \Phi(z)_{11}$ , which is invariant under monodromy and regular at z = 0. Since dim Ker  $(T - \mathrm{id}) = 1$ , it is unique up to scaling, and  $\phi_0(z) = \sum_{n=0}^{\infty} \frac{(5n)!z^n}{(n!)^5}$ . We next obtain  $\phi_1 = \Phi(z)_{12}$  s.t.  $\phi_1(e^{2\pi i}z) = \phi_1(z) + 2\pi i\phi_0(z)$ , which is unique up to multiples of  $\phi_0$ . Since  $\Phi(z) = S(z) \exp(R \log z)$ ,  $\phi_1(z) = \phi_0(z) \log z + \tilde{\phi}(z)$ , with  $\tilde{\phi}(z)$  holomorphic. Now

(20) 
$$\Theta^{j}(f(z)\log z) = (\Theta^{j}f)\log z + j(\Theta^{j-1}f)$$

If we write  $F(x) = x^4 - 5z \prod_{i=1}^{4} (5x + j)$ , then

(21) 
$$\mathcal{D}\phi_1(z) = F(\Theta)(\phi_0(z)\log z + \tilde{\phi}(z)) \\ = (F(\Theta)\phi_0)\log z + F'(\Theta)\phi_0 + F(\Theta)\tilde{\phi}$$

Since  $0 = \mathcal{D}\phi_0 = \mathcal{D}\phi_1$ , we find  $\mathcal{D}\tilde{\phi}(z) = -F'(\Theta)\phi_0(z)$ . This gives a recurrence relation on the coefficients of  $\tilde{\phi}(z)$ , and one obtains:

(22) 
$$\tilde{\phi}(z) = 5 \sum_{n=1}^{\infty} \frac{(5n)!}{(n!)^5} \left( \sum_{j=n+1}^{5n} \frac{1}{j} \right) z^n$$

We want canonical coordinates on the moduli space of complex structures: there are  $\beta_0, \beta_1 \in H_3(\check{X}, \mathbb{Z})$ , with monodromy  $\beta_0 \mapsto \beta_0, \beta_1 \mapsto \beta_1 + \beta_0$ , and

(23) 
$$\int_{\beta_0} \check{\Omega} = C\phi_0(z)$$
$$\int_{\beta_1} \check{\Omega} = C'\phi_0(z) + C''\phi_1(z)$$

The monodromy acts on the latter by  $\int_{\beta_1} \check{\Omega} \mapsto \int_{\beta_1 + \beta_0} \check{\Omega}$ , implying that  $2\pi i C'' = C$ . Thus, the canonial coordinates are

$$(24)$$

$$w = \frac{\int_{\beta_1} \check{\Omega}}{\int_{\beta_0} \check{\Omega}}$$

$$= \frac{C'}{C} + \frac{1}{2\pi i} \frac{\phi_1}{\phi_0}$$

$$= \frac{1}{2\pi i} \log c_2 + \frac{1}{2\pi i} \log z + \frac{1}{2\pi i} \frac{\check{\phi}}{\phi_0}$$

$$q = \exp(2\pi i w) = c_2 z \exp\left(\frac{\check{\phi}(z)}{\phi_0(z)}\right)$$

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 10

#### DENIS AUROUX

# 1. The Quintic (contd.)

Recall that we had a quintic mirror family  $\check{X}_{\psi}$  with LCSL degeneration as  $z = (5\psi)^{-5} \to 0$ . We had the Picard-Fuchs equation for periods of  $\check{\Omega}$ , and found 2 solutions given by

(1) 
$$\phi_0(z) = \sum_{n=0}^{\infty} \frac{(5n)!}{(n!)^5} z^n$$

$$\phi_1(z) = \phi_0(z) \log z + \tilde{\phi}(z), \, \tilde{\phi}(z) = 5 \sum_{n=1}^{\infty} \frac{(5n)!}{(n!)^5} \left( \sum_{j=n+1}^{5n} \frac{1}{j} \right) z^n$$

We then obtained canonical coordinates  $\beta_0, \beta_1 \in H_3(\check{X}, \mathbb{Z})$  for the complex moduli space s.t. the monodromy preserves  $\beta_0$  and maps  $\beta_1 \mapsto \beta_1 + \beta_0$ , and  $\int_{\beta_i} \check{\Omega}$  are linear combinations of  $\phi_0, \phi_1$ . We wrote

(2) 
$$w = \frac{\int_{\beta_1} \check{\Omega}}{\int_{\beta_0} \check{\Omega}}, q = \exp(2\pi i w) = c_2 z \exp\left(\frac{\tilde{\phi}(z)}{\phi_0(z)}\right)$$

where  $c_2$  is a normalization constant.

# 1.1. Yukawa coupling on $H^{2,1}(\check{X})$ . Let

(3) 
$$W_k = \int_{\check{X}_z} \check{\Omega}(z) \wedge \frac{d^k}{dz^k} \check{\Omega}(z)$$

We can rewrite the Picard-Fuchs equation in the form

(4) 
$$\frac{d^4}{dz^4} [\check{\Omega}] + \sum_{k=0}^3 c_k(z) \frac{d^k}{dz^k} [\check{\Omega}] = 0$$

Then  $W_4 + \sum_{k=0}^3 c_k W_k = 0$ . By Griffiths transversality  $(\frac{d^k}{dz^k}\check{\Omega}$  has no (0,3)-component unless  $k \geq 3$ ,  $W_0 = W_1 = W_2 = 0$ . Moreover,

(5) 
$$0 = \frac{d^2}{dz^2} W_2 = \int_{\check{X}} \frac{d^2 \check{\Omega}}{dz^2} \wedge \frac{d^2 \check{\Omega}}{dz^2} + 2 \int_{\check{X}} \frac{d \check{\Omega}}{dz} \wedge \frac{d^3 \check{\Omega}}{dz^3} + \int_{\check{X}} \check{\Omega} \wedge \frac{d^4 \check{\Omega}}{dz^4}$$
$$= 0 + 2 \left( \frac{dW_3}{dz} - W_4 \right) + W_4$$

implying that  $W_4 = 2W_3'$ , hence  $W_3'(z) = -\frac{1}{2}c_3(z)W_3(z)$ . Looking at the coefficients on the Picard-Fuchs equation gives

(6) 
$$c_3(z) = \frac{6}{z} - \frac{2 \cdot 5^5}{1 - 5^5 z} \implies (\log W_3') = \frac{-3}{z} + \frac{5^5}{1 - 5^5 z} \\ \implies W_3(z) = \frac{c_1}{(2\pi i)^3 z^3 \cdot (5^5 z - 1)}$$

We next normalize  $\check{\Omega}$ : scaling by f(z) changes

(7) 
$$\langle \frac{\partial}{\partial z}, \frac{\partial}{\partial z}, \frac{\partial}{\partial z} \rangle = \int f \check{\Omega} \wedge \left( \frac{d^3}{dz^3} f \check{\Omega} \right) = f^2 \int \check{\Omega} \wedge \frac{d^3 \check{\Omega}}{dz^3}$$

We want to scale by  $\frac{1}{\int_{\beta_0} \check{\Omega}} = \frac{\text{const}}{\phi_0(z)}$ , giving

(8) 
$$\langle \frac{\partial}{\partial z}, \frac{\partial}{\partial z}, \frac{\partial}{\partial z} \rangle = \frac{c_1}{(2\pi i)^3 z^3 \cdot (5^5 z - 1)\phi_0(z)^2}$$

Switching to  $\frac{\partial}{\partial w} = \left(\frac{dw}{dz}\right)^{-1} \frac{\partial}{\partial z}$  gives us

(9) 
$$\langle \frac{\partial}{\partial w}, \frac{\partial}{\partial w}, \frac{\partial}{\partial w} \rangle = \frac{c_1}{(5^5 z - 1)\phi_0(z)^2 \delta(z)^3}$$

where

(10) 
$$\delta(z) = 2\pi i z \frac{dw}{dz} = z \frac{d}{dz} (\log q) = 1 + z \frac{d}{dz} \left( \frac{\tilde{\phi}(z)}{\phi_0(z)} \right)$$

To express this as a power series in q:

(11) 
$$\frac{dq}{dz} = q \frac{d \log q}{dz} = \frac{q}{z} \delta(z) = c_2 \delta(z) \exp\left(\frac{\tilde{\phi}(z)}{\phi_0(z)}\right) \\
\frac{d^j}{dq^j} \langle \frac{\partial}{\partial w}, \frac{\partial}{\partial w}, \frac{\partial}{\partial w} \rangle = \left(\frac{1}{c_2 \delta(z) \exp(\tilde{\phi}/\phi_0)} \frac{d}{dz}\right)^j \left(\frac{c_1}{(5^5 z - 1)\phi_0(z)^2 \delta(z)^3}\right)$$

Solving and expanding out, we obtain

$$(12) \quad \langle \frac{\partial}{\partial w}, \frac{\partial}{\partial w}, \frac{\partial}{\partial w} \rangle = -c_1 - 575 \frac{c_1}{c_2} q - \frac{1950750}{2} \frac{c_1}{c_2^2} q^2 - \frac{10277490000}{6} \frac{c_1}{c_2^3} q^3 + \cdots$$

Now we can describe the mirror symmetry: there exists a basis of  $H^2(X,\mathbb{Z}) \cong \mathbb{Z}$  (where X is the original quintic) given by the Poincaré dual  $\{e\}$  of a hyperplane s.t., writing  $[B+i\omega]=te, q=\exp(2\pi it)=\exp(2\pi i\int_{line}B+i\omega)$ , the mirror map is

(13) 
$$q \leftrightarrow q, w = \frac{1}{2\pi i} \log q \leftrightarrow t, \frac{\partial}{\partial w} \leftrightarrow \frac{\partial}{\partial t} = e$$

where the latter correspondence is how we match  $H^{2,1}(\check{X}) = T\mathcal{M}_{cx}(\check{X}) \cong T\mathcal{M}_{Kah}(X) \cong H^{1,1}(X)$ . Recall that

(14) 
$$\langle e, e, e \rangle = \int_X e \wedge e \wedge e + \sum_{d > 0} \langle e, e, e \rangle_{0,d} q^d$$

where  $\langle e, e, e \rangle_{0,d}$  is the Gromov-Witten invariant  $(\int_d e)(\int_d e)(\int_d e)N_d = d^3N_d$  of degree d rational curves through three general hyperplanes, and  $N_d = \sum_{d=kd'} \frac{n_{d'}}{k^3}$  counts multiple covers. Expanding out, we obtain

$$\langle e, e, e \rangle = 5 + \sum_{d>0} d^3 N_d q^d = 5 + \sum_{d>0} d^3 n_3 \frac{q^d}{1 - q^d}$$

$$= 5 + n_1 q + 8 \left( n_2 + \frac{n_1}{8} \right) q^2 + 27 \left( n_3 + \frac{n_1}{27} \right) q^3 + 64 \left( n_4 + \frac{n_2}{8} + \frac{n_1}{64} \right) q^4 + \cdots$$

Matching these gives

- $c_1 = -5$ .
- $n_1 = \frac{575 \cdot 5}{c_2} = \frac{2875}{c_2}$ : classical algebraic geometry tells us that 2875 is the number of lines on a quintic,  $c_2 = 1$ .
- $n_2 = 609250$  (had been calculated by Sheldon Katz, 1986)
- $n_3 = 317206375$  (Ellingsrud-Stromme, 1990)
- $\bullet$   $n_4 = 242467530000$

The general verification is in the proof of mirror symmetry for the quintic by Givental and Lian-Liu-Yau separately around 1996 (more generally, they verify for Calabi-Yau complete intersections in toric varieties).

### 2. Homological Mirror Symmetry

This is a different mathematical formulation of mirror symmetry, given by Kontsevich in 1994. On the symplectic side, just as J-holomorphic curves gave a "quantum" intersection product on  $H^*(X)$ , we will look at intersections of Lagrangian submanifolds, and obtain a "quantum" intersection theory involving J-holomorphic disks. On the complex side, we look at intersections of subvarieties and holomorphic maps/extensions of bundles/sheaves. Thus, the complex side is governed by "classical" algebraic geometry, and all the "quantum" information is on the symplectic side. For this, we will construct the Fukaya  $(A_{\infty})$ -category,

which is roughly the category whose objects are Lagrangian submanifolds, whose morphisms are intersections, and whose algebraic structures (differential, product, etc.) are governed by J-holomorphic disks. On the complex side, we just have coherent sheaves, and our mirror symmetry will give an equivalence of derived categories.

Future question: what is the relationship between this form of mirror symmetry and our previous one? Basic answer: open string theory gave an idea of considering submanifolds with boundary lying on branes. Kontsevich himself looked at the Hochschild cohomologies of the two categories above, which give the "big" quantum cohomology and the cohomology ring of polyvector fields on the respective sides.

2.1. Lagrangian Floer Homology. Let  $(M, \omega)$  be a symplectic manifold,  $L_0, L_1$  compact Lagrangian submanifolds. Assume that  $L_0, L_1$  intersect transversely, i.e.  $L_0 \cap L_1$  is a finite set. Recall that we defined the Novikov ring as  $\Lambda = \{\sum a_i T^{\lambda_i} \mid \lambda_i \to \infty\}$ . The Floer complex  $CF(L_0, L_1)$  is the free  $\Lambda$ -module  $\Lambda^{|L_0 \cap L_1|}$  generated by  $L_0 \cap L_1$ . Our goal is to define a differential  $\delta$  s.t.  $HF(L_0, L_1) = H^*(CF, \delta)$  is invariant under Hamiltonian isotopies. The motivation for this was to understand Arnold's conjecture on Lagrangian intersections. From that point of view, HF is an obstruction to displacement of Lagrangians: in general, if we have a topological isotopy between two Lagrangian submanfiolds, a pair of intersections can be cancelled along a Whitney disk (its corners are the intersections of the two Lagrangian submanifolds; Hamiltonian isotopies cancel intersection along holomorphic Whitney disks.  $\delta$  will count holomorphic disks M between Lagrangian submanifolds.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 11

## DENIS AUROUX

0.1. Lagrangian Floer Homology (contd). Let  $(M, \omega)$  be a symplectic manifold,  $L_0, L_1$  compact Lagrangian submanifolds. Formally, Floer homology is Morse theory for the action functional on the path space  $\mathcal{P}(L_0, L_1)$ , which has as critical points the constant paths. More precisely, the actual functional is a map  $\tilde{A}: \tilde{\mathcal{P}}(L_0, L_1) \to \mathbb{R}$ , where  $\tilde{\mathcal{P}}(L_0, L_1)$  is the universal cover of the path space, i.e. pairs  $(\gamma, [u])$  where  $\gamma$  is a path between  $L_0$  and  $L_1$  and [u] is a homotopy between  $\gamma$  and some fixed base path \*. Then  $\mathcal{A}(\gamma, [u]) = \int u^* \omega$ , and for v a vector field along  $\gamma$ ,

(1) 
$$d\mathcal{A}(\gamma) \cdot v = \int_{[0,1]} \omega(\dot{\gamma}, v) dt = \int_{[0,1]} g(J\gamma, v) dt = \langle J\dot{\gamma}, v \rangle_{L^2}$$

The critical points are contant paths  $\dot{\gamma} = 0$ , and the gradient flow lines are *J*-holomorphic curves  $\frac{\partial \gamma}{\partial s} = -J\dot{\gamma}$ .

However, no one has managed to run this Morse theory rigorously. The actual setup assumes  $L_0, L_1$  are transverse, and as before, define the Novikov ring as  $\Lambda = \{ \sum a_i T^{\lambda_i} \mid \lambda_i \to \infty \}$  and the Floer complex  $CF(L_0, L_1)$  as the free  $\Lambda$ -module  $\Lambda^{|L_0\cap L_1|}$  generated by  $L_0\cap L_1$ . We look at  $u:\mathbb{R}\times [0,1]\to M$  equipped with a compatible almost-complex structure J s.t.

- $\overline{\partial}_J u = 0$ , or  $\frac{\partial u}{\partial s} + J \frac{\partial u}{\partial t} = 0$ .  $u(s,0) \in L_0, u(s,1) \in L_1$
- $\lim_{s \to +\infty} u(s,t) = p$ ,  $\lim_{s \to -\infty} u(s,t) = q$  for  $\{p,q\} \subset L_0 \cap L_1$   $E(u) = \int u^* \omega = \int \int_{\mathbb{R} \times [0,1]} \left| \frac{\partial u}{\partial s} \right|^2 ds dt < \infty$ .

We consider the space of solutions  $\mathcal{M}(p,q,[u],J)$  for fixed  $p,q\in L_0\cap L_1,[u]$  a homotopy class as above, and J a given almost-complex structure. The above problem is a Fredholm problem, and the expected dimension of  $\mathcal{M} = \operatorname{ind}(\partial_J)$  is called the Maslov index. The Maslov index comes from  $\pi_1(\bigwedge Gr) = \mathbb{Z}$ . Explicitly, let  $L_0, L_1(t)_{t \in [0,1]}$  be Lagrangian subspaces of  $\mathbb{R}^{2n}$  s.t.  $L_1(0), L_1(1)$  intersect  $L_0$ transversely. The Maslov index of  $(L_1(t); L_0)$  is the number of times that  $L_1(t)$ is non-transverse to  $L_0$  with mutlipliticities and signs. For instance, for  $L_0$  $\mathbb{R}^n \subset \mathbb{C}^n$ ,  $L_1(t) = (e^{i\theta_1(t)}\mathbb{R}) \times \cdots \times (e^{i\theta_n(t)}\mathbb{R})$  with all  $\theta_i$ 's increasing past 0, the Maslov index is n. In general, given a homotopy u, we can trivialize  $u^*TM$ , and  $u^*|_{\mathbb{R}\times 0}(TL_0), u^*|_{\mathbb{R}\times 1}(TL_1)$  are 2 paths of Lagrangian subspaces. We can trivialize so that  $TL_0$  remains constant, and  $\operatorname{ind}(u)$  is the Maslov index of the path  $TL_1$  relative to  $TL_0$  as one goes from p to q.

Now, we want to define

(2) 
$$\partial(p) = \sum_{\substack{q \in L_0 \cap L_1 \\ \phi \in \pi_2(M, L_0 \cup L_1) \\ \operatorname{ind}(\phi) = 1}} \#(\mathcal{M}(p, q, \phi, J) / \mathbb{R}) T^{\omega(\phi)} \cdot q$$

The issues that arise are: transversality, compactness and bubbling, the orientation of  $\mathcal{M}$ , and whether  $\partial^2 = 0$ .

**Theorem 1.** If  $[\omega] \cdot \pi_2(M) = 0$  and  $[\omega] \cdot \pi_2(M, L_i) = 0$ , then  $\partial$  is well-defined,  $\partial^2 = 0$ , and  $HF(L_0, L_1) = H^*(CF, \partial)$  is independent of the chosen J and invariant under Hamiltonian isotopies of  $L_0$  and/or  $L_1$ .

Corollary 1. If  $[\omega] \cdot \pi_2(M, L) = 0$  and  $\psi$  is a Hamiltonian diffeomorphism s.t.  $\psi(L), L$  are transverse,  $\#(\psi(L) \cap L) \geq \sum b_i(L)$ .

This is a special case of Arnold's conjecture: the rough idea is that  $H^*(L) \cong HF(L, \psi(L))$  and  $\operatorname{rk} CF \geq \operatorname{rk} HF$ .

Example. Consider  $T^*S_1 \cong \mathbb{R} \times S^1$ , with  $L_0 = \{(0,\theta) | \theta \in S^1 = [0,2\pi)\}$ ,  $L_1 = \{(a\sin\theta+b,\theta)\}$ . Then  $L_0 \cap L_1 = \{p,q\}$ , and the region between them decomposes into disks u,v. Then  $CF(L_0,L_1) = \bigwedge p \oplus \bigwedge q$ ,  $\partial(p) = (T^{area(u)} - T^{area(v)})q$ ,  $\partial(q) = 0$ . In this case  $(c_1(TM) = 0$ , as is the Maslov class of  $L_i$ ),  $\exists$  a  $\mathbb{Z}$  grading on CF (because the index is independent of [u]), e.g. deg p = 0, deg q = 1. We have two cases:

- if area(u) = area(v), then  $\partial = 0, HF(L_0, L_1) \cong H^*(S^1, \Lambda)$ .
- if  $area(u) \neq area(v)$ , then  $HF(L_0, L_1) = 0$ .

Return to our issues, one can achieve transversality for simple maps by picking J generic, but for multiply covered maps, we need sophisticated techniques such as domain-dependent J, multivalued perturbations, virtual cycles, or Kuranishi structures. To obtain an orientation of the moduli space, we need auxiliary data, e.g. a spin structure on  $L_0, L_1$ . For compactness, the Gromov compactness theorem implies that, given an energy bound, compactness holds after adding limiting configurations. There are three types of phenomena:

- Bubbling of spheres: if  $|du_n| \to \infty$  at an interior point, the resulting limit is a spherical bubble. The treatment is the same as in Gromov-Witten invariants, and in good cases (if transversality is achieved), the congurations with sphere bubbles have real codimension  $\geq 2$  in  $\overline{\mathcal{M}}$ .
- Bubbling of disks: if  $|du_n| \to \infty$  at a boundary point, the resulting limit is a disk bubble at the boundary. Even assuming transversality, the space of these will have real codimension 1 in  $\overline{\mathcal{M}}$ .

• Breaking of strips: if energy escapes towards  $s \to \pm \infty$ , i.e. reparameterizing  $u_n(\cdot - \delta_n, \cdot)$  for  $|\delta_n| \to \infty$  gives different limits, the resulting limit is a sequence of holomorphic strips (that is, what was a single holomorphic strip with progressively thinning "necks" becomes several separate strips).

Finally, we want to have  $\partial^2 = 0$ . Assuming no bubbling, we consider  $\mathcal{M}(p, q, \phi, J)/\mathbb{R}$  for J generic,  $\phi \in \pi_2$ ,  $\operatorname{ind}(\phi) = 2$ . We expect a one-dimensional manifold, which is compactified by adding broken trajectories, i.e.

(3) 
$$\Gamma \in L_0 \cap L_1 \quad (\mathcal{M}(p, r, \phi_1, J)/\mathbb{R}) \times (\mathcal{M}(p, r, \phi_2, J)/\mathbb{R})$$

$$\sigma_1 \# \sigma_2 = \sigma$$

The gluing theorem states that the resulting  $\overline{\mathcal{M}(p,q,\phi,J)/\mathbb{R}}$  is a manifold with boundary. Now, the number of ends of a compact oriented 1-manifold is 0, and thus so are the contributions to the coefficients of  $T^{\omega(\phi)}q$  in  $\partial^2(p)$ .

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 12

## DENIS AUROUX

0.1. Lagrangian Floer Homology (contd). Let  $(M, \omega)$  be a symplectic manifold,  $L_0, L_1$  compact Lagrangian submanifolds intersecting transversely. We defined  $CF(L_0, L_1) = \Lambda^{|L_0 \cap L_1|}$  and the differential

(1) 
$$\partial(p) = \sum_{\substack{q \in L_0 \cap L_1 \\ \phi \in \pi_2(M, L_0 \cup L_1) \\ \operatorname{ind}(\phi) = 1}} \#(\mathcal{M}(p, q, \phi, J) / \mathbb{R}) T^{\omega(\phi)} \cdot q$$

where  $\mathcal{M}$  is the set of finite energy J-holomorphic maps  $u : \mathbb{R} \times [0,1] \to M, u(s,0) \in L_0, u(s,1) \in L_1, \lim_{s\to+\infty} u = p, \lim_{s\to-\infty} u = q$ . The limits of sequences in  $\mathcal{M}$  exhibit sphere bubbling, disk bubbling, and broken strips. If there was no bubbling (e.g.  $\omega \cdot \pi_2(M, L_i) = 0$ , we stated that  $\partial^2 = 0$ .

Example. Consider  $T^*\mathbb{R} \cong \mathbb{R}^2$  again, with  $L_0$  the zero section and  $L_1$  the unit circle intersecting  $L_0$  at points p = (1,0), q = (-1,0). Then  $CF(L_0, L_1) = \Lambda p \oplus \Lambda q$ ,  $\partial(p) = \pm T^{\omega(u)}q$ ,  $\partial(q) = \pm T^{\omega(v)}p$ , and  $\partial^2 \neq 0$ . We have an index  $2 \mathcal{M}(p,p)$  isomorphic to the interval, consisting of holomorphic maps whose image is the unit disk with a slit entering at the point p and ending at a position  $\alpha \in (-1,1)$ . More precisely, using the upper half of the unit disk as our domain, we can write  $u_{\alpha}(z) = \frac{z^2 + \alpha}{1 + \alpha z^2}$ . There are two endpoints:  $\alpha \to -1$ , in which we obtain a broken trajectory  $p \to q \to p$ , and  $\alpha \to 1$ , where we obtain the constant strip at p and a disk bubble.

0.2. More about grading. Question: can we define deg (p), deg (q) s.t. deg (q) deg (p) = ind([u])? Maslov index comes from  $\pi_1(\Lambda Gr) \cong \mathbb{Z}$ : if  $2c_1(M) = 0$ , then the  $\Lambda Gr$ -bundle of Lagrangian planes in TM has a fiberwise universal cover, the  $\Lambda Gr$ -bundle of "graded Lagrangian planes". Then, if at  $p \in L_0 \cap L_1$ , we fix graded lifts of  $T_pL_0, T_pL_1$ , then deg (p) is the Maslov index at p. Locally, in the basic configuration  $L_0 = \mathbb{R}^n \subset \mathbb{C}^n, L_1 = (e^{-i\theta}\mathbb{R})^n \subset \mathbb{C}^n$  for small  $\theta$ , deg (p) = 0: in general, deg (p) will be the Maslov index of the path from this reference configuration.

The obstructions to the existence of a global graded lift of L are  $2c_1(TM)$  and, if it vanishes, the Maslov class  $\mu_L \in H^1(L, \mathbb{Z})$ . If the latter vanishes as well, then the index  $\operatorname{ind}(u) = \operatorname{deg}(q) - \operatorname{deg}(p)$  independently of [u] and HF is  $\mathbb{Z}$ -graded. If

we have nonzero Maslov class, we can do modifications at the boundary of u away from p,q to change the index. In such a case, we find that HF is  $\mathbb{Z}/N\mathbb{Z}$  graded, where N is the minimal Maslov number (if  $L_i$  are oriented, N is always even, so can reduce to a  $\mathbb{Z}/2\mathbb{Z}$  grading which coincides with the signs of intersections  $L_1 \cdot L_0$ ). We can also work over a larger graded ring, with a new parameter that keeps track of how the index of the strip differs from the difference of degrees. In the monotone case, i.e. when the area and the Maslov index are proportional to each other, we just need to assign our parameter T some nonzero degree.

0.3. Hamiltonian isotopy invariance. Say  $H:[0,1]\times M\to\mathbb{R}$  generates  $\phi_H^t=$  the flow of  $X_H$  ( $\iota_{X_H}\omega=dH$ ).

**Proposition 1.** If there is no bubbling, then  $HF^*(\phi_H^1(L_0), L_1) \cong HF^*(L_0, L_1)$ .

We want to count finite energy  $(E(u) = \iint \left| \frac{\partial u}{\partial s} \right|^2)$  solutions of:

(2) 
$$u : \mathbb{R} \times [0, 1] \to M$$
$$\frac{\partial u}{\partial s} + J(\frac{\partial u}{\partial t} - \beta(s)X_H(t, u)) = 0$$
$$u(s, 0) \in L_0, u(s, 1) \in L_1$$

where  $\beta$  is a cutoff function that goes to 0 for  $s \gg 0$ , 1 for  $s \ll 0$ . For  $s \to +\infty$ , u converges to a point in  $L_0 \cap L_1$ , while for  $s \to -\infty$ , it converges to a trajectory  $\dot{\gamma}(t) = X_H(t,\gamma), \gamma(0) \in L_0, \gamma(1) \in L_1 \Leftrightarrow \gamma(1) \in \phi_H^1(L_0) \cap L_1$ . If  $\tilde{u}(s,t) = \phi_H^{(t,1)}(u(s,t))$ , then we can modify  $J \mapsto \tilde{J}$  to obtain  $\frac{\partial \tilde{u}}{\partial s} + \tilde{J} \frac{\partial \tilde{u}}{\partial t} = 0$  for  $s \ll 0$ . Counting isolated index 0 solutions gives  $\Psi_H : CF(L_0, L_1) \to CF(\phi_H(L_0), L_1)$ . In the absence of bubbling, we can show that  $\Psi_H$  is a chain map, i.e.  $\Psi_H \circ \partial = \partial' \circ \Psi_H$  (look at the index 1 moduli space, with the ends given by broken trajectories). The breaking of strips can occur at  $s \to -\infty$ , where we obtain a  $\tilde{J}$ -holomorphic strip contributing to  $\partial'$  between  $\phi_H(L_0)$  and  $L_1$ , or at  $s \to +\infty$ , where we obtain a J-holomorphic strip contributing to  $\partial$  between  $L_0$  and  $L_1$ . The signed number of ends of a 1-manifold is 0, so the contributions of  $\Psi_H \circ \partial$ ,  $\partial' \circ \Psi_H$  cancel out. Then  $\Psi_H$  induces a map on HF. To see that it is an isomorphism, we build a homotopy  $\Theta$  between  $\Psi_{-H} \circ \Psi_H$  and id, i.e.  $\Psi_{-H} \circ \Psi_H - \mathrm{id} = \partial \circ \Theta + \Theta \circ \partial$ .

Example. Let  $M = T^*N$ ,  $\omega = \sum dp_i \wedge dq_i$ . Equip N with a Riemannian metric g which induces a metric and almost-complex structure on  $T^*N$ : along the zero section,  $TM = TN \oplus T^*N$  (the two components isomorphic via g), and  $J = \begin{pmatrix} 0 & -I \\ I & 0 \end{pmatrix}$ . Let  $L_0$  be the zero section,  $L_1$  the graph of  $\epsilon df$  for  $\epsilon > 0$  small, f a Morse function on N, Morse-Smale for g. Then  $L_0 \cap L_1$  is the set of critical points of f, and the Maslov index is n— the Morse index.

**Theorem 1** (Fukaya-Oh et al). For  $\epsilon \to 0$ , holomorphic strips between  $L_0$  and  $L_1$  are in one-to-one correspondence with the gradient trajectories of f, and  $HF^*(L_0, L_1) \cong HM_{n-*}(f) \cong H^*(N)$ .

 $(L_0, L_1)$  are exact Lagrangian, hence  $\omega \cdot \pi_2 = 0$ , and all strips  $p \to q$  have  $\int u^*\omega = \epsilon(f(p) - f(q))$ , so we can forget about T up to  $\tilde{p} = T^{\epsilon f(p)}p$ .) By the Weinstein Lagrangian neighborhood theorem, this is a universal local calculation. If L doesn't bound any holomorphic disks in M,  $HF(L, L) = HF(L, \psi(L)) = H^*(L, \Lambda)$ . Otherwise, we can try to filter CF,  $\partial$  by the symplectic area of disks, e.g. if L is monotone  $(\omega, c_1)$  positively proportional on  $\pi_2(M, L)$ . Then we get the CF spectral sequence which starts at CF and converges to CF to CF.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 13

## DENIS AUROUX

0.1. Lagrangian Floer Homology (contd). Let  $(M, \omega)$  be a symplectic manifold,  $L_0, L_1$  compact Lagrangian submanifolds intersecting transversely. We defined  $CF(L_0, L_1) = \Lambda^{|L_0 \cap L_1|}$  and the differential

(1) 
$$\partial(p) = \sum_{\substack{q \in L_0 \cap L_1 \\ \phi \in \pi_2(M, L_0 \cup L_1) \\ \operatorname{ind}(\phi) = 1}} \#(\mathcal{M}(p, q, \phi, J) / \mathbb{R}) T^{\omega(\phi)} \cdot q$$

where  $\mathcal{M}$  is the set of finite energy J-holomorphic maps  $u: \mathbb{R} \times [0,1] \to M, u(s,0) \in L_0, u(s,1) \in L_1, \lim_{s \to +\infty} u = p, \lim_{s \to -\infty} u = q.$ 

0.2. **Product Structure.** We want to define a map

(2) 
$$CF^*(L_0, L_1) \otimes CF^*(L_1, L_2) \to CF^*(L_0, L_2)$$

Look at  $u: D^2 \to M$  a J-holomorphic disk whose image is a triangle between  $L_0, L_1, L_2$ . Mark points  $1, j, j^2$  on the boundary, with  $u(j) = p \in L_0 \cap L_1, u(j^2) = q \in L_1 \cap L_2, u(1) = r \in L_0 \cap L_2$ , and  $u([1,j]) \subset L_0, u([j,j^2]) \subset L_1, u([j^2,1]) \subset L_2$ . Removing our three points from the disk gives a space biholomorphic to a pair of pants, i.e. a Riemann surface with boundary with 3 strip-like ends. Now, let  $\mathcal{M}(p,q,r,[u],J)$  be the set of such maps: as a moduli space, its expected dimension is  $\operatorname{ind}([u]) = \operatorname{deg}(r) - (\operatorname{deg}(p) + \operatorname{deg}(q))$  (trivialize  $u^*TM$ , and pick graded lifts of  $TL_i$ :  $\operatorname{deg}(p)$  is the Maslov index of the path from the reference setup from last time to  $T_pL_0, T_pL_1$ ).

**Definition 1.** (Assuming transversality)

(3) 
$$q \circ p = \sum_{\substack{r \in L_0 \cap L_2 \\ \operatorname{ind}([u]) = 0}} (\# \mathcal{M}(p, q, r, [u], J)) T^{\omega(u)} r$$

Note. As usual, this assumes transversality and orientability of moduli spaces. Moreover,  $\operatorname{Aut}(D^2)$  acts freely transitively on ordered triples of boundary points, so  $(1,j,j^2)$  is arbitrary. Finally, the lack of symmetry of the index formula in p,q,r is because the degree deg  $(r) \in CF^*(L_0,L_2)$  is  $n-\deg (r \in CF(L_2,L_0))$ . Recall that our reference frame as  $R^n, (e^{-i\theta}\mathbb{R})^n \subset \mathbb{C}^n$ , which we stated to have

index 0 for  $\theta > 0$  small: the reversed frame  $(e^{-i\theta}\mathbb{R})^n$ ,  $\mathbb{R}^n$  has index n. In general, we have a "Poincaré duality"  $CF^*(L, L') \cong CF^{n-*}(L', L)^{\vee}$  compatible with our operations (e.g. differentials are dual).

**Proposition 1.** If  $[\omega] \cdot \pi_2(M, L_i) = 0$ , then the product structure defined above satisfies the Leibniz rule w.r.t.  $\partial$ , and hence induces a product on  $HF^*$ ; this product structure will be associative.

For the Leibniz rule: consider index 1 moduli spaces (triangles with edges segments of  $L_0, L_1, L_2$  and corners p, q, r as above). We compactify by adding limit configurations, specifically bubblings of disks and broken configurations (where we get the same broken strips at our strip-like ends). Our strip may break at p, q, or r, giving us contributions  $q \circ (\partial p), (\partial q) \circ p, \partial (q \circ p)$  respectively. Since the number of ends of an oriended 1-manifold with boundary is 0, we have  $\partial (q \circ p) = \pm (\partial q) \circ p \pm q \circ (\partial (p))$ . Thus, p, q closed implies that

(4) 
$$\partial(q \circ p) = \pm(\partial q) \circ p \pm q \circ (\partial(p)) = 0$$

so  $q \circ p$  is closed as well. Moreover, if  $p = \partial p'$  is exact, so is

(5) 
$$q \circ p = \pm \partial (q \circ p') \pm (\partial q) \circ p' = \pm \partial (q \circ p')$$

Thus, we have a well-defined product on  $HF^*$ .

We also have higher-order operations

(6) 
$$CF^*(L_0, L_1) \otimes \cdots \otimes CF^*(L_{k-1}, L_k) \stackrel{m_k}{\to} CF^*(L_0, L_k)[2-k]$$

(a grading shift). Note that  $m_1 = \partial$ , and  $m_2$  is my product above. To obtain these, look at J-holomorphic maps from disks  $D^2$  with k+1 marked points  $z_0, \ldots, z_k$  on the boundary (cyclically ordered distinct, not fixed in advance), s.t. the image under u is a disk between  $L_0, \ldots, L_k$  with  $u(z_0) = q \in L_0 \cap L_k, u(z_i) = p_i \in L_{i-1} \cap L_i$ . Repeating the above procedure, we obtain a moduli space  $\mathcal{M}(p_1, \ldots, p_k, q, [u], J)$  with expected dimension deg  $(q) - (\sum \deg p_i) + k - 2$ , where the k-2 comes from the dimension of the moduli space of disks with (k+1) marked points. Assuming orientability and transversality,

(7) 
$$m_k(p_k, \dots, p_1) = \sum_{\substack{q \in L_0 \cap L_k \\ \text{ind}([u]) = 0}} (\# \mathcal{M}(p_1, \dots, p_k, q, [u], J)) T^{\omega(u)} q$$

Remark. The moduli space  $\mathcal{M}_{0,k+1}$  of disks with (k+1) boundary marked points (distinct, in order, modulo  $\mathbb{D}^2$  automorphisms) is contractible of dimension k-2, and compactifies to  $\overline{\mathcal{M}}_{0,k+1}$ , the moduli space of stable genus 0 Riemann surfaces with one boundary component, k+1 boundary marked points. That is, they are trees of disks attached at marked nodal points such that each component carries at least 3 special points. For instance,  $\overline{\mathcal{M}}_{0,4}$  has general point given by 4 points

on the boundary of a unit disk. WLOG, we can set the first three at three fixed points, and let the fourth move between the first and the third. When it hits either of these points, we force bubbling at the boundary and obtain two limiting configurations, and our moduli space is a line segment with two boundary points corresponding to them. In general, the objects we obtain are associahedra.

Thus, when considering sequences of (k+1)-marked holomorphic disks, the limiting configurations allowed by Gromov compactnness are those with bubbling of spheres or disks, breaking of strips at marked points, and degeneration of the domain to  $\partial \overline{\mathcal{M}}_{0,k+1}$ . We get relations by considering 1-dimensional moduli spaces.

**Proposition 2.** Assuming no bubbling of disks and spheres,  $\forall m \geq 1, (p_1, \ldots, p_m), p_i \in L_{i-1} \cap L_i$ ,

(8) 
$$\sum_{\substack{k,\ell \geq 1 \\ k+\ell = m+1 \\ 0 < j < \ell-1}} (-1)^* m_{\ell}(p_m, \dots, p_{j+k+1}, m_i(p_{j+k}, \dots, p_{j+1}), p_j, \dots, p_1) = 0$$

where  $* = \deg(p_1) + \cdots + \deg(p_i) + j$ .

For instance, we obtain

(9) 
$$m_1(m_1(p)) = 0$$

$$m_1(m_2(p,q)) + (-1)^{\deg q+1} m_2(m_1(p),q) + m_2(p,m_1(q)) = 0$$

$$m_1(m_3(p,q,r)) \pm m_2(m_2(p,q),r) \pm m_2(p,m_2(q,r))$$

$$\pm m_3(m_1(p),q,r) \pm m_3(p,m_1(q),r) \pm m_3(p,q,m_1(r)) = 0$$

which says that  $m_1$  is a differential,  $m_2$  satisfies the Leibniz rule, and  $m_2$  is associative up to homotopy given by  $m_3$  (i.e. it is associative in  $HF^*$ ).

*Proof.* Idea: consider a 1-dimensional moduli space  $\mathcal{M}(p_1,\ldots,p_m,q,[u],J)$  and its ends. Transversality and no bubbling implies that our limiting configurations come from bubbling on  $\mathcal{M}_{0,k+1}$  (i.e. nearby points colliding). Setting the total number of ends (with orientation) to be zero gives us the sum of terms in the proposition.

**Definition 2.** An  $A_{\infty}$  category is a linear "category" where morphism spaces are equipped with algebraic operations  $(m_k)_{k\geq 1}$  satisfying the  $A_{\infty}$ -relations (those defined above).

The Fukaya category will be the  $A_{\infty}$ -category whose objects are Lagrangian submanifolds (with extra data), the morphisms are Floer complexes, and the algebraic operations are as above.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 14

## DENIS AUROUX

0.1. Lagrangian Floer Homology (contd). Let  $(M, \omega)$  be a symplectic manifold,  $L_0, L_1$  compact Lagrangian submanifolds intersecting transversely. Recall that the complexes  $CF(L_0, L_1) = \Lambda^{|L_0 \cap L_1|}$  carry a differential  $m_1$ , product  $m_2$ , and higher operations

$$(1) CF^*(L_0, L_1) \otimes \cdots \otimes CF^*(L_{k-1}, L_k) \stackrel{m_k}{\to} CF^*(L_0, L_k)[2-k]$$

We looked at *J*-holomorphic maps u from disks  $D^2$  with marked boundary points to disks in the manifold between  $L_0, \ldots, L_k$  with  $u(z_0) = q \in L_0 \cap L_k, u(z_i) = p_i \in L_{i-1} \cap L_i$ . We find that the expected dimension of our manifold  $\mathcal{M}(p_1, \ldots, p_k, q, [u], J)$  is deg  $q - (\deg p_1 + \cdots \deg p_k) + k - 2$ . Assuming transversality,

(2) 
$$m_k(p_k, \dots, p_1) = \sum_{\substack{q \in L_0 \cap L_k \\ \text{ind}([u]) = 0}} (\# \mathcal{M}(p_1, \dots, p_k, q, [u], J)) T^{\omega(u)} q$$

By looking at the  $\partial$  (1-dimensional moduli space), we obtained the  $A_{\infty}$  relations:

**Proposition 1.** Assuming no bubbling of disks and spheres,  $\forall m \geq 1, (p_1, \ldots, p_m), p_i \in L_{i-1} \cap L_i$ ,

(3) 
$$\sum_{\substack{k,\ell \geq 1 \\ k+\ell = m+1 \\ 0 < j < \ell-1}} (-1)^* m_{\ell}(p_m, \dots, p_{j+k+1}, m_k(p_{j+k}, \dots, p_{j+1}), p_j, \dots, p_1) = 0$$

where 
$$* = \deg(p_1) + \cdots + \deg(p_j) + j$$
.

This implies that  $m_1$  is a differential,  $m_2$  satisfies the Leibniz rule, and  $m_2$  is associative up to homotopy given by  $m_3$  (i.e. it is associative in  $HF^*$ ).

**Definition 1.** An  $A_{\infty}$  category is a linear "category" where morphism spaces are equipped with algebraic operations  $(m_k)_{k\geq 1}$  satisfying the  $A_{\infty}$ -relations (those defined above).

In our case, we have the following categories:

- A Fukaya category is any of a number of  $A_{\infty}$  categories whose objects are Lagrangian submanifolds (with extra data), the morphisms are Floer complexes, and the algebraic operations are as above.
- So far we only have an ' $A_{\infty}$ -precategory" because the homomorphisms have only been defined for transverse pairs of objects.
- At the homology level, we can also define the *Donaldson-(Fukaya cate-gory)* whose homomorphisms are the cohomologies HF, so that composition is automatically associative. This is technically easier, but we lose some information that we need for mirror symmetry.
- We eventually want to define our Fukaya category to be over  $\mathbb{C}$ , rather than over the Novikov ring. So far, we have counted disks with weights  $T^{\omega(u)} \in \Lambda$ , and Gromov compactness tells us that there are only finitely many contributions below a certain area. That is, the sums may be infinite, but they converge in the Novikov ring. Physicists usually write the terms as  $e^{-2\pi\omega(u)} \in \mathbb{R}$  instead of  $T^{\omega(u)}$ , and hope for convergence. Changing the value of T is equivalent to rescaling the symplectic form, i.e. working over  $\Lambda$  is equivalent to working with a family M, ( $\omega_t = t\omega$ ), with  $T = e^{-2\pi t}$ . We thus work near the large volume limit  $t \to \infty$  and compute Floer homologies for all t simultaneously. We call this the "convergent power series" Floer homology: even when defined, this is often not Hamiltonian isotopy invariant.
- For Lagrangians  $L_i$  equipped with  $(E_i, \nabla_i) \to L_i$  complex vector bundles with flat (unitary) connections. We think of these as local systems of coefficients on our Lagrangians. We define an associated complex with twisted coefficients:

(4) 
$$CF((L_0, E_0, \nabla_0), (L_1, E_1, \nabla_1)) = \bigoplus_{p \in L_0 \cap L_1} \text{Hom}((E_0)_p, (E_1)_p) \otimes \Lambda$$
  
for  $L_0, L_1$  transverse. Then given  $p_1, \dots, p_k, p_i \in L_{i-1} \cap L_i, w_1, \dots, w_k, w_i \in \text{Hom}((E_{i-1})_{p_i}, (E_i)_{p_i})$ , we let

(5)
$$m_{k}(w_{k},...,w_{1}) = \sum_{\substack{q \in L_{0} \cap L_{k} \\ \text{ind}([u]) = 0}} (\#\mathcal{M}(p_{1},...,p_{k},q,[u],J))T^{\omega(u)}\mathcal{P}_{[\partial u]}(w_{k},...,w_{1})$$

where 
$$\mathcal{P}_{[\partial u]}(w_k, \dots, w_1) \in \text{Hom}((E_0)_q, (E_k)_q)$$
 is defined by

(6) 
$$\mathcal{P}_{[\partial u]}(w_k, \dots, w_1) = \gamma_k \circ w_k \circ \gamma_{k-1} \circ \dots \circ \gamma_1 \circ w_1 \circ \gamma_0$$

where parallel transport along  $\partial u$  from  $q \to p_1$  gives  $\gamma_0 \in \text{Hom}((E_0)_q, (E_0)_{p_1})$ , and similarly parallel transport from  $p_i \to p_{i+1}$  using  $\nabla_i$  gives  $\gamma_i \in \text{Hom}((E_i)_{p_i}, (E_i)_{p_{i+1}})$ . For  $\nabla_i$  flat, this only depends on  $[\partial u]$ . In particular, if  $E_i$  is the topologically trivial line bundle  $\mathbb{C} \times L_i$  and  $\nabla_i$  is a flat U(1)

connection (up to gauge equivalence),  $\nabla_i = d + iA_i$  for  $A_i$  a closed 1-form, this encodes the data of holonomies  $\pi_1(L_i) \to U(1)$ . Then, using trivializations, we get  $CF = \Lambda_{\mathbb{C}}^{|L_0 \cap L_1|}$  with generators  $p, w = \mathrm{id} : E_{0_p} \to E_{1_p}$  and  $m_k$  counts disks with weight  $T^{\omega(u)} \cdot \mathrm{hol}(\partial u)$ , where

(7) 
$$\operatorname{hol}(\partial u) = \exp\left(i\sum_{j=0}^{k} \int_{\partial u_j} A_j\right)$$

is the holonomy of parallel transport.

We can now construct our first iteration of the Fukaya category:

- The objects are  $\mathcal{L} = (L, E, \nabla)$ , where L is a compact spin Lagrangian ( $\mathbb{Z}$ -graded:  $\mu_L = 0$  with grading data) and  $(E, \nabla)$  a flat hermitian vector bundle
- The morphisms for transverse  $\mathcal{L}_0, \mathcal{L}_1$  is given by  $\hom(\mathcal{L}_0, \mathcal{L}_1) = CF^*$ . Issues:
  - (1) What if  $L_0$  is not transverse to  $L_1$  (in particular, if  $L_0 = L_1$ )?
  - (2) What if L bounds disks?

For the first problem, see Seidel's book: the idea is to use a Hamiltonian perturbation  $\phi_H$  to get  $L_1$  to be transverse to  $L_0$ , and define  $CF^*(L_0, L_1)$  to be generated by  $L_0 \cap \phi_H(L_1)$  (the vector bundles carry without change). We perturb all the  $\overline{\partial}$ equations by suitable terms: in the strip-like ends, we have  $\frac{\partial u}{\partial s} + J(\frac{\partial u}{\partial t} + X_H(u)) =$ 0 for  $H = H(L_{i-1}, L_i)$ . We need a procedure to associate to (L, L') a Hamltonian H(L, L'), and to a sequence  $L_0, \ldots, L_k$  some compatible perturbation data, and further to show that different choices give equivalent  $A_{\infty}$ -categories. Note that this will not be strictly unital, and will only get a homology unit.

Alternatively, one can use "Morse-Bott" Floer theory (e.g. FOOO). We define  $CF^*(L,L) = C_*(L;\Lambda)$  to be the space of singular chains on L: when defining the operations  $m_k$ , instead of strip-like ends, we have a marked point z on the boundary such that when evaluating at z, and require u(z) to be in the chain. For instance, in the product  $m_2$ , one considers disks with boundary points  $z_0, z_1, z_2$  with three evaluation maps  $\operatorname{ev}_i : \overline{\mathcal{M}}_{0,3}(M, L; J, \beta) \to L$ ,

(8) 
$$m_2(C_2, C_1) = \sum_{\beta \in \pi_2(X, L)} T^{\omega(\beta)}(ev_0)_*([\overline{\mathcal{M}}_{0,3}(M, L; J, \beta)] \cap ev_1^*C_1 \cap ev_2^*C_2)$$

For the class  $\beta = 0$ , we find that the contribution of constant disks gives the intersection product on  $C_*(L)$ . The higher  $m_k$  follow similarly, though  $m_1$  does not allow  $\beta = 0$  and adds the classical  $\partial C$  instead. More generally, if  $L_0 \cap L_1$  have a "clean intersection" (i.e.  $L_0 \cap L_1$  is smooth), then we set  $CF^*(L_0, L_1) = C_*(L_0 \cap L_1; \Lambda)$ .

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 15

## DENIS AUROUX

## 1. Lagrangian Floer Homology (contd)

Recall first our approaches to  $CF^*(L,L)$  with the  $A_\infty$  algebraic structure:

- (1) Hamiltonian perturbations  $CF^*(L, L) = \Lambda^{|L \cap \phi_H(L)|}$
- (2) FOOO:  $CF^*(L, L) = C_*(L, \Lambda)$  the space of "chains" on L. We have evaluation maps  $\operatorname{ev}_i : \overline{\mathcal{M}}_{0,k+1}(M, L; J, \beta) \to L$ , giving multiplication maps

$$m_k(C_k,\ldots,C_1) = \sum_{\beta \in \pi_2(X,L)} T^{\omega(\beta)}(\operatorname{ev}_0)_*([\overline{\mathcal{M}}_{0,k+1}(M,L;J,\beta)] \cap ev_1^*C_1 \cap \cdots \cap ev_k^*C_k)$$

- (3) Cornea-Lalonde approach: "clusters". Pick a Morse function  $f: L \to \mathbb{R}$ , and set  $CF^*(L, L) = \Lambda^{\operatorname{crit}(f)}$ .  $m_k$  counts "clusters" of J-holomorphic disks and gradient flowlines.
- 1.1. **Disks and Obstruction.** We've seen that, if  $L_0$  or  $L_1$  bound holomorphic disks, then  $\partial^2 \neq 0$  (the moduli space of index 2 strips has disk bubbling on the boundaries in addition to strips). Counting the contribution of disk bubbles gives  $m_0 \in CF^*(L, L)$ . In FOOO theory,  $m_0 = \sum_{\beta \neq 0} \operatorname{ev}_*[\overline{\mathcal{M}}_{0,1}(M, L; J, \beta)] \cdot T^{\omega(\beta)}$ . A bubble on the boundary of the disk on  $L_1$  is  $m_2(m_0, p)$ , for  $p \in CF^*(L_0, L_1)$ ,  $m_0 \in CF^*(L_1, L_1)$ . Hence  $m_0$  is the obstruction to  $\partial^2 = 0$ . More generally,  $A_{\infty}$ -equations still hold if we include the terms  $m_k(\cdots, m_0, \cdots)$ , which we can interpret as disks with k+1 marked points developing disk bubbles on the boundary. This is called a "curved  $A_{\infty}$ -category". We say that L is unobstructed if  $m_0 = 0$ , and weakly unobstructed if  $m_0 \in \Lambda.1_L$ , where  $1_L$  is the fundamental chain [L]. This implies centrality, and  $m_1^2 = 0$  on CF(L, L). Weakly unobstructed L's with a given "charge" form an honest  $A_{\infty}$ -category.

In FOOO, one tries to cancel the obstruction by a formal deformation  $b \in CF^1(L, L)$ . For  $\nabla = d + b$  on  $CF^*(L, L)$ , write

(1) 
$$m_k^b(C_k,\ldots,C_1) = \sum m_{k+\ell}(b\ldots b,c_k,b\ldots b,\ldots,b\ldots b,c_1,b\cdots b)$$

This is still a curved  $A_{\infty}$ -algebra, and we look for b, s.t.  $m_0^b = m_0 + m_1(b) + m_2(b,b) + \cdots = 0$ . Such a b is called a "bounding cochain". One can similarly define weakly bounding cochains, and define our obmjects to be equivalence classes of pairs (L,b) for b a weakly bounding cochain.

- 1.2. Coherent Sheaves on a Complex Manifold. Let X be a complex manifold,  $\mathcal{O}_X$  the sheaf of holomorphic functions on X. Recall that a coherent sheaf  $\mathcal{F}$  is a sheaf of  $\mathcal{O}_X$ -modules s.t.
  - $\mathcal{F}$  is of finite type, i.e. there is an open cover by affines  $U_i$  s.t.  $\mathcal{F}_{U_i}$  is generated by a finite number of sections, i.e.  $\exists$  surjective maps  $\mathcal{O}_X|_{U_i}^{\oplus n} \to \mathcal{F}|_{U_i}$ .
  - For all  $U \subset X$  open,  $\phi : \mathcal{O}_X|_U^{\oplus n} \to \mathcal{F}|_U$  a homomorphism of  $\mathcal{O}_X$ -module, Ker  $\phi$  is of finite type.

If X is nice enough,  $\mathcal{F}$  has finite presentation, i.e.  $\exists$  an open cover s.t. there is an exact sequence

(2) 
$$\mathcal{O}_X^{\oplus r}|_U \to \mathcal{O}_X^{\oplus n}|_U \to \mathcal{F}|_U \to 0$$

i.e. a coherent sheaf is the cokernel of a morphism of vector bundles. Coherent sheaves form an abelian category, i.e. they contain kernels and cokernels.

Example. Any vector bundle E can be thought of as a locally free sheaf of holomorphic sections. For D a hypersurface defined by s = 0 for s a section of some line bundle  $\mathcal{L}$ , we have a short exact sequence

$$(3) 0 \to \mathcal{L}^{-1} \stackrel{s}{\to} \mathcal{O}_X \to \mathcal{O}_D \to 0$$

For  $Z \subset X$  a codimension r subvariety defined transversely as  $s^{-1}(0)$ , for s a section of a rank r vector bundle  $\mathcal{E}$ , we have a Koszul resolution

$$(4) 0 \to \bigwedge^r \mathcal{E}^* \stackrel{s}{\to} \bigwedge^{r-1} \mathcal{E}^* \stackrel{s}{\to} \cdots \stackrel{s}{\to} \mathcal{E}^* \stackrel{s}{\to} \mathcal{O}_X \to \mathcal{O}_Z \to 0$$

For X smooth (proper?), coherent sheaves always have a finite resolution by vector bundles.

The category of sheaves has both an internal  $\mathscr{H}$  (which is a sheaf) and an external Hom (just a group, and in fact the global sections for the former). A functor  $F: \mathcal{C} \to \mathcal{C}'$  is left exact if  $0 \to A \to B \to C \to 0 \implies 0 \to F(A) \to F(B) \to F(C)$ . If the category  $\mathcal{C}$  has enough injectives (objects such that  $\operatorname{Hom}_{\mathcal{C}}(-,I)$  is exact), there are right-derived functors  $R^iF$  s.t.

$$(5) \qquad 0 \to F(A) \to F(B) \to F(C) \to R^1 F(A) \to R^1 F(B) \to R^1 F(C) \to \cdots$$

To compute  $R^iF(A)$ , resolve A by injective objects as  $0 \to A \to I^0 \to I^1 \to I^2 \to \cdots$ , we get a complex  $0 \to F(I^0) \to F(I^1) \to F(I^2) \to \cdots$ . Taking cohomology gives  $R^iF(A) = \text{Ker }(F(I^i) \to F(I^{i+1}))/\text{im }(F(I^{i-1}) \to F(I^i))$ . Note that  $R^0F(A) = F(A)$ .

Example. Sheaf cohomology arises as the right derived functor of the global section functor, and can be computed by acyclic sheaves (e.g. flasque sheaves).

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 16

## DENIS AUROUX

0.1. Coherent Sheaves on a Complex Manifold (contd.) Let X be a complex manifold,  $\mathcal{O}_X$  the sheaf of holomorphic functions on X. Recall that the category of sheaves has both an internal  $\mathscr{H}om$  (which is a sheaf) and an external Hom (the group of global sections for the former). A functor  $F: \mathcal{C} \to \mathcal{C}'$  is left exact if  $0 \to A \to B \to C \to 0 \implies 0 \to F(A) \to F(B) \to F(C)$ . If the category  $\mathcal{C}$  has enough injectives (objects such that  $\operatorname{Hom}_C(-, I)$  is exact), there are right-derived functors  $R^iF$  s.t.

$$(1) 0 \to F(A) \to F(B) \to F(C) \to R^1 F(A) \to R^1 F(B) \to R^1 F(C) \to \cdots$$

To compute  $R^iF(A)$ , resolve A by injective objects as  $0 \to A \to I^0 \to I^1 \to I^2 \to \cdots$ , we get a complex  $0 \to F(I^0) \to F(I^1) \to F(I^2) \to \cdots$ . Taking cohomology gives  $R^iF(A) = \text{Ker }(F(I^i) \to F(I^{i+1}))/\text{im }(F(I^{i-1}) \to F(I^i))$ . Note that  $R^0F(A) = F(A)$ .

We stated last time that sheaf cohomology arises as the right-derived functor of the global sections functor. Moreover, since  $\operatorname{Hom}(\mathcal{E}, -)$  and  $\operatorname{Hom}(-, \mathcal{E})$  are both left-exact (the first covariant, the second contravariant), we can define  $\operatorname{Ext}^i = R^i\operatorname{Hom}$ , and short exact sequences  $0 \to \mathcal{F}_1 \to \mathcal{F}_2 \to \mathcal{F}_3 \to 0$  give

(2) 
$$0 \to \operatorname{Hom}(\mathcal{E}, \mathcal{F}_1) \to \operatorname{Hom}(\mathcal{E}, \mathcal{F}_2) \to \operatorname{Hom}(\mathcal{E}, \mathcal{F}_3) \\ \to \operatorname{Ext}(\mathcal{E}, \mathcal{F}_1) \to \operatorname{Ext}(\mathcal{E}, \mathcal{F}_2) \to \operatorname{Ext}(\mathcal{E}, \mathcal{F}_3) \to \cdots$$

while sequences  $0 \to \mathcal{E}_1 \to \mathcal{E}_2 \to \mathcal{E}_3 \to 0$  give

(3) 
$$0 \to \operatorname{Hom}(\mathcal{E}_3, \mathcal{F}) \to \operatorname{Hom}(\mathcal{E}_2, \mathcal{F}) \to \operatorname{Hom}(\mathcal{E}_1, \mathcal{F}) \\ \to \operatorname{Ext}(\mathcal{E}_3, \mathcal{F}) \to \operatorname{Ext}(\mathcal{E}_2, \mathcal{F}) \to \operatorname{Ext}(\mathcal{E}_1, \mathcal{F}) \to \cdots$$

Moreover, if  $\mathcal{E}$  is a locally free sheaf,  $\mathscr{H}om(\mathcal{E}, -)$  is exact, and  $\operatorname{Ext}^{i}(\mathcal{E}, \mathcal{F}) = H^{i}(\mathscr{H}om(\mathcal{E}, \mathcal{F}))$ . Otherwise, we can resolve  $\mathcal{E}$  by locally free sheaves

$$(4) 0 \to E_n \to \cdots \to E_0 \to \mathcal{E} \to 0$$

and, for all practical purposes, replace  $\mathcal{E}$  by the complex  $E_n \to \cdots \to E_0$ . In our case, we obtain a sequence  $\mathscr{H}om(E_0,\mathcal{F}) \to \cdots \to \mathscr{H}om(E_n,\mathcal{F})$  whose hypercohomology gives  $\operatorname{Ext}^*(\mathcal{E},\mathcal{F})$ .

Example. Let  $\mathcal{E}$  be a locally free sheaf,  $\mathcal{O}_p$  the skyscraper sheaf at a point p. Then  $\mathscr{H}om(\mathcal{E},\mathcal{O}_p)\cong\mathcal{E}^*|_p$  is the skyscraper sheaf with stalk  $\mathcal{E}_p^*$  at p. Taking sheaf cohomology gives  $\operatorname{Hom}(\mathcal{E},\mathcal{O}_p)\cong\mathcal{E}_p^*$ ,  $\operatorname{Ext}^i(\mathcal{E},\mathcal{O}_p)=0\ \forall\ i\geq 1$ . Furthermore,  $\mathscr{H}om(\mathcal{O}_p,\mathcal{O}_p)\cong\mathcal{O}_p$ : to obtain the higher Ext groups, we resolve  $\mathcal{O}_p$  by locally free sheaves. (WLOG) Assuming X is affine, local coordinates near p define a section s of  $\mathcal{O}_X^{\oplus n}\cong V$   $(n=\dim X)$  vanishing transversely at p. We then have a long exact sequence

(5) 
$$0 \to \left(\bigwedge^n V^* \stackrel{s}{\to} \bigwedge^{n-1} V^* \stackrel{s}{\to} \cdots \stackrel{s}{\to} V^* \stackrel{s}{\to} \mathcal{O}_X\right) \to \mathcal{O}_p \to 0$$

Applying  $\mathscr{H}om(-,\mathcal{O}_p)$ , we get

(6) 
$$\mathcal{O}_p \xrightarrow{0} V \otimes \mathcal{O}_p \xrightarrow{0} \cdots \xrightarrow{0} \bigwedge^{n-1} V \otimes \mathcal{O}_p \xrightarrow{0} \bigwedge^n V \otimes \mathcal{O}_p$$

(the maps are all zero, since all the sheaves are all skyscraper sheaves at p). Ext\* $(\mathcal{O}_p, \mathcal{O}_p)$  is the hypercohomology of this complex, i.e.

(7) 
$$\operatorname{Ext}^{k}(\mathcal{O}_{p}, \mathcal{O}_{p}) \cong H^{0}(\bigwedge^{k} V \otimes \mathcal{O}_{p}) \cong \bigwedge^{k} V_{p}$$

Similarly,  $\operatorname{Ext}^i(\mathcal{O}_p,\mathcal{E})$  can be computed by hypercohomology of

(8) 
$$\mathcal{E} \to \stackrel{s}{\to} V \otimes \mathcal{E} \stackrel{s}{\to} \bigwedge^{2} V \otimes \mathcal{E} \stackrel{s}{\to} \cdots \stackrel{s}{\to} \bigwedge^{n} V \otimes \mathcal{E}$$

which is the Koszul resolution of the skyscraper sheaf with stalk  $\bigwedge^n V \otimes \mathcal{E}$  at p. This sequence is exact except in the last place, and the cokernel is a skyscraper sheaf with stalk  $\bigwedge^n \otimes \mathcal{E}$  at p. Thus,  $\operatorname{Ext}^n(\mathcal{O}_p, \mathcal{E}) \cong (\bigwedge^n V \otimes \mathcal{E})_p$  with all other groups zero. This is consistent with the Serre duality  $\operatorname{Ext}^i(\mathcal{E}, \mathcal{F}) \cong \operatorname{Ext}^{n-i}(\mathcal{F}, K_X \otimes \mathcal{E})^{\vee}$ .

- 0.2. **Derived Categories.** The general idea is to work with complexes up to homotopy.
  - Enlarging a category to include complexes makes it algebraically nicer (e.g. the derived category is *triangulated*) and less sensitive to the initial set of objects (we can restrict to a nice subcategory). For instance, for Fukaya categories, one can hope to allow objects like immersed Lagrangians implicitly.
  - Even if we know how to define general objects, it is usually easier to replace them with complexes of nice objects. For instance, for  $s \in H^0(\mathcal{L}), D = s^{-1}(0)$ , we can exchange  $\mathcal{O}_D$  with the complex  $\{\mathcal{L}^{-1} \stackrel{s}{\to} \mathcal{O}_X\}$ .

Example. This makes it easier to perform intersection theory: for  $D_1, D_2$  defined by sections  $s_1, s_2$  of  $\mathcal{L}_1, \mathcal{L}_2$ , their homological intersection is

(9) 
$$[D_1] \cdot [D_2] = c_1(\mathcal{L}_1) \cup c_1(\mathcal{L}_2) \cap [X] = c_1(\mathcal{L}_1|_{D_2}) \cdot [D_2]$$

If  $D_1$  and  $D_2$  intersect transversely,  $\mathcal{O}_{D_1 \cap D_2} = \mathcal{O}_{D_1} \otimes \mathcal{O}_{D_2}$ . We can also resolve this using the associated complex, i.e. apply  $-\otimes \mathcal{O}_{D_2}$  to  $\{\mathcal{L}_1^{-1} \stackrel{s_1}{\to} \mathcal{O}_{D_2}\}$ , obtaining  $\{\mathcal{L}_1^{-1}|_{D_2} \stackrel{s_1|_{D_2}}{\to} \mathcal{O}_{D_2}\}$ . If  $D_1 = D_2 = D$ ,  $\mathcal{O}_D \otimes \mathcal{O}_D = \mathcal{O}_D$  is "too big" (because  $\otimes$  is right exact but not exact). Using the associated complex still works, however, as we obtain  $\{\mathcal{L}_1^{-1}|_D \stackrel{s|_D=0}{\to} \mathcal{O}_D\}$  with kernel  $\mathcal{L}^{-1}|_D$  and cokernel  $\mathcal{O}_D$ .

• When do we consider two complexes to be isomorphic? Having isomorphic cohomology is not enough. For instance, in algebraic topology, a theorem of Whitehead states that, for X, Y simply connected simplicial complexes, X and Y are homotopy equivalent  $\Leftrightarrow \exists Z$  and simplical maps  $X \to Z, Y \to Z$  s.t. the chain maps  $C^*(Z) \to C^*(X), C^*(Z) \to C^*(Y)$  are isomorphisms in cohomology.

**Definition 1.** A chain map  $f: C_* \to D_*$  (i.e. a collection of maps  $f_iC_i \to D_i$  commuting with  $\partial$ ) is a quasi-isomorphism if the induced maps on cohomology are isomorphisms.

This is stronger than  $H^*(C_*) \cong H^*(D_*)$ .

Example. The complexes of  $\mathbb{C}[x,y]$ -modules  $\mathbb{C}[x,y]^{\oplus 2} \to_{(x,y)} \mathbb{C}[x,y]$  and  $\mathbb{C}[x,y] \to_0 \mathbb{C}$  have the same cohomology but are not quasi-isomorphic.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 17

## DENIS AUROUX

## 1. Coherent Sheaves on a Complex Manifold (contd.)

We now recall the following definitions from category theory.

**Definition 1.** An additive category is one in which  $\operatorname{Hom}(A,B)$  are abelian groups, composition is distributive, and there is a direct sum  $\oplus$  and a zero object 0. An abelian category is an additive category s.t. every morphism has a kernel and cokernel, e.g. a kernel of  $f: A \to B$  is a morphism  $K \to A$  s.t.  $g: C \to A$  factors through K uniquely iff  $f \circ g = 0$ .

One can define complexes in an additive category, but one needs to be in an abelian category to have notions of exact sequences and cohomology. Recall that, given chain complexes  $C_*$ ,  $D_*$ , a chain map  $f: C_* \to D_*$  is a collection of maps  $f_iC_i \to D_i$  commuting with  $\delta$ . Given two such maps  $f = \{f_i\}$ ,  $g = \{g_i\}$ , we call them homotopic if there is a map  $h: A \to B[-1]$  (B shifted down by 1) s.t.  $f - b = d_B h + h d_A$ , i.e.

$$(1) \qquad A_{i-1} \xrightarrow{d_{i-1}} A_i \xrightarrow{d_i} A_{i+1} A_i \xrightarrow{d_{i+1}} \cdots$$

$$f_{i-1} \bigvee g_{i-1} \xrightarrow{h_i} f_i \bigvee g_i \xrightarrow{h_i} f_{i+1} \bigvee g_{i+1} \xrightarrow{d_{i+1}} \cdots$$

$$B_{i-1} \xrightarrow{d_{i-1}} B_i \xrightarrow{d_i} B_{i+1} \xrightarrow{d_i} \cdots$$

A chain map is a quasi-isomorphism if the induced maps on cohomology are isomorphisms. This is stronger than  $H^*(C_*) \cong H^*(D_*)$ . For  $\mathcal{A}$  an abelian category, the category of bounded chain complexes is the differential graded category whose objects are bounded chain complexes in  $\mathcal{A}$  and whose morphisms are "pre-homomorphisms" of complexes  $\operatorname{Hom}^k(A_*, B_*) = \bigoplus_i \operatorname{Hom}_{\mathcal{A}}(A_i, B_{i+k})$ : it is equipped with a differential  $\delta$  where

(2) 
$$f \in Hom^k(A_*, B_*) \implies \delta(f) = d_B f + (-1)^{k+1} f d_A \in Hom^{k+1}(A_*, B_*)$$

Chain maps are precisely the elements of Ker ( $\delta$ : Hom<sup>0</sup>  $\rightarrow$  Hom<sup>1</sup>), and the nullhomotopic maps are elements of im ( $\delta$ : Hom<sup>-1</sup>  $\rightarrow$  Hom<sup>0</sup>), so  $H^0$ Hom(A, B) gives the space of chain maps up to homotopy.

**Definition 2.** For  $\mathcal{A}$  an abelian category, the bounded derived category  $D^b(\mathcal{A})$  is the triangulated category whose objects are bounded chain complexes in  $\mathcal{A}$  and

whose morphisms are given by chain maps up to homotopy localizing w.r.t. quasi-isomorphisms. That is, quasi-isomorphisms are formally inverted; for any quasi-isomorphism s, we add a morphism  $s^{-1}$ . More precisely,  $\operatorname{Hom}_{D^b(\mathcal{A})}(A_*, B_*) = \{A \stackrel{s}{\leftarrow} A' \stackrel{f}{\rightarrow} B\}/\sim \text{where s is a quasi-isomorphism, f is a chain map, and } \sim \text{is homotopy equivalence. We similarly define the categories } D^+(\mathcal{A}), D^-(\mathcal{A}) \text{ of chain complexes bounded above/below.}$ 

To explain the notion of triangulated category, recall the following:

• In the category of topological spaces (or simplicial complexes), there are no kernels and cokernels. Given a map f, however, the mapping cone  $C_f = (X \times [0,1]) \sqcup Y/(x,0) \sim (x',0), (x,1) \sim f(x)$  acts as both simultaneously. There are natural maps  $i: Y \to C_f$  (inclusion) and  $q: C_f \to \Sigma X$  (collapsing Y), and we obtain a sequence of topological spaces

(3) 
$$X \xrightarrow{f} Y \xrightarrow{i} C_f \xrightarrow{q} \Sigma X \to \cdots$$

with compositions null-homotopic. This gives a long exact sequence of

$$(4) \quad H_i(X) \to H_i(Y) \to H_i(C_f) \to H_i(\Sigma X) = H_{i-1}(X) \to H_i(\Sigma Y) = H_{i-1}(Y)$$

- If X, Y are simplicial complexes, f a simplicial map, C<sub>f</sub> defined analogously is a simplicial complex, with i-cells given by cones on (i − 1)-cells of X and i-cells of Y. The boundary map is given by the matrix (∂<sub>X</sub> 0 f ∂<sub>Y</sub>).
  If A\* and B\* are complexes, f a chain map, we define C<sub>f</sub> = A[1] ⊕ B,
- If  $A^*$  and  $B^*$  are complexes, f a chain map, we define  $C_f = A[1] \oplus B$ , i.e.  $C_f^i = A^{i+1} \oplus B^i$ . The boundary map is  $\delta = \begin{pmatrix} \delta_A[1] & 0 \\ f & \delta_B \end{pmatrix}$ . Note that, if A, B are single objects,  $\operatorname{Cone}(f : A \to B)$  is just  $\{0 \to A \xrightarrow{f} B \to 0\}$ . We have natural chain maps  $B^* \xrightarrow{i} C_f^*$  (subcomplex) and  $C_f^* \xrightarrow{q} A^*[1]$  (quotient complex). As before,  $A^*[1]$  is quasi-isomorphic to  $\operatorname{Cone}(i : B^* \to C_f^*)$ .
- Finally, in the derived category, the inversion of quasi-isomorphisms gives us *exact triangles*

$$\begin{array}{c}
A^* \longrightarrow B \\
 & \\
 & \\
C^*
\end{array}$$

with

(6) 
$$H^i(A) \to H^i(B) \to H^i(C) \to H^{i+1}(A) \to \cdots$$

**Definition 3.** A triangulated category is an additive category with a shift functor [1] and a set of distinguished triangles satisfying various axioms:

- $\forall X, X \stackrel{\text{id}}{\to} X \to 0 \to X[1]$  is distinguished,
- $\forall X \to Y$ , there is a distinguished triangle  $X \xrightarrow{u} Y \to Z \to X[1]$  (Z is called the mapping cone of f).
- The rotation of any distinguished triangle is distinguished, i.e. for  $X \to Y \to Z \to X[1]$  distinguised,  $Y \to Z \to X[1] \to Y[1]$  and  $Z \to X[1] \to Y[1] \to Z[1]$  are distinguished.
- Given a square

$$(7) \qquad X \xrightarrow{f} Y \\ \downarrow \qquad \downarrow \\ X' \xrightarrow{f'} Y$$

there is a map between the mapping cones of f, f' that makes everything commute in the induced map of distinguished triangles

(8) 
$$X \longrightarrow Y \longrightarrow Z \longrightarrow X[1]$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$X' \longrightarrow Y' \longrightarrow Z' \longrightarrow X'[1]$$

• Given a pair of maps  $X \xrightarrow{u} Y \xrightarrow{v} Z$ , there are maps between the mapping cones  $C_u, C_v, C_{v \circ u}$  of u, v, and  $v \circ u$  that make every commute in the induced maps of distinguished triangles.

- 1.1. **Derived functors.** Let  $F : \mathcal{A} \to \mathcal{B}$  be a left exact functor between abelian categories.  $\mathcal{R} \subset \mathcal{A}$  is called an *adapted class of objects* for F if
  - $\mathcal{R}$  is stable under direct sums,
  - for  $C^*$  an acyclic complex of objects in  $\mathcal{R}$ ,  $F(C^*)$  is acyclic, and
  - $\forall A \in \mathcal{A}, \exists R \in \mathcal{R} \text{ s.t. } 0 \to A \xrightarrow{i} R.$

For instance, the set of injective objects is such an adapted class. Let  $K^+(\mathcal{R})$  be the homotopy category of complexes bounded below of objects in  $\mathcal{R}$ . RF gives a composition  $D^+(\mathcal{A}) \to K^+(\mathcal{R}) \xrightarrow{F} D^+(\mathcal{B})$ , where the first map is induced by resolution by objects of R. The map  $D^+(\mathcal{A}) \to D^+(\mathcal{B})$  is exact, i.e. it maps exact triangles to exact triangles, and  $R^iF = H^i(RF)$ .

1.2. **Extensions.** Let  $A, B \in \mathcal{A} \hookrightarrow D^b(\mathcal{A})$  be single object complexes concentrated in degree 0, so B[k] is conentrated in degree -k.

**Proposition 1.**  $\operatorname{Hom}_{D^b(\mathcal{A})}(A, B[k]) = \operatorname{Ext}_{\mathcal{A}}^k(A, B)$ .

We can use this to define a product  $\operatorname{Ext}_{\mathcal{A}}^k(A,B) \otimes \operatorname{Ext}_{\mathcal{A}}^\ell(B,C) \to \operatorname{Ext}_{\mathcal{A}}^{k+\ell}(A,C)$  as a composition  $A \to B[k] \to C[k+\ell]$  in  $D^b(\mathcal{A})$ .

Example. For k = 1, we have

$$\begin{array}{cccc}
0 \longrightarrow 0 \longrightarrow A \longrightarrow 0 \\
\downarrow & \downarrow \\
0 \longrightarrow B \longrightarrow 0 \longrightarrow 0
\end{array}$$

There are no chain maps, but we can invert quasi-isomorphisms. If we have an extension  $0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0$  in  $\mathcal{A}$ , we have chain maps

$$\begin{array}{cccc}
0 \longrightarrow 0 \longrightarrow C \longrightarrow 0 \\
& & & & & & \\
g & & & & \\
0 \longrightarrow A \stackrel{f}{\longrightarrow} B \longrightarrow 0 \\
& & & & \\
\downarrow & & & \\
0 \longrightarrow A \longrightarrow 0 \longrightarrow 0
\end{array}$$

giving an element in  $\operatorname{Hom}_{D^b(\mathcal{A})}(C, A[1]) = \operatorname{Ext}^1(C, A)$ .

There are two ways to understand the above proposition. First, if  $\mathcal{A}$  has enough injectives, take a resolution of B by a complex  $I^0 \to I^1 \to \cdots$  quasi-isomorphic to B: the chain maps from A to  $I^*$  are, up to homotopy, isomorphic to  $H^k(\operatorname{Hom}(A, I^*)) \cong \operatorname{Ext}^k(A, B)$ . Second, we can check the definition of a derived functor. Given a short exact sequence  $0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0$  in  $\mathcal{A}$ , we get an exact triangle  $A \xrightarrow{f} B \xrightarrow{g} C \xrightarrow{w} A[1]$  quasi-isomorphic to a distinguished triangle with  $\operatorname{Cone}(f)$ .

**Proposition 2.** For an exact triangle  $A \xrightarrow{f} B \xrightarrow{g} C \xrightarrow{h} A[1]$  and an object E, we have long exact sequences

(12)

$$\cdots \to \operatorname{Hom}(E,A[i]) \xrightarrow{f_*} \operatorname{Hom}(E,B[i]) \xrightarrow{g_*} \operatorname{Hom}(E,C[i]) \xrightarrow{h_*} \operatorname{Hom}(E,A[i+1]) \to \cdots$$

$$\cdots \to \operatorname{Hom}(A[i+1], E) \xrightarrow{h^*} \operatorname{Hom}(C[i], E) \xrightarrow{g^*} \operatorname{Hom}(B[i], E) \xrightarrow{f^*} \operatorname{Hom}(A[i], E) \to \cdots$$

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 18

## DENIS AUROUX

## 1. Derived Fukaya Category

Last time: derived categories for abelian categories (e.g.  $D^b \text{Coh}(X)$ ). This time: the derived Fukaya category. We start with an  $A_{\infty}$ -category  $\mathcal{A}$  and obtain a triangulated category via "twisted complexes". Recall that in an  $A_{\infty}$ -category,  $hom_A(X,Y)$  is a graded vector space equipped with maps

(1) 
$$m_k : \hom_{\mathcal{A}}(X_0, X_1) \otimes \cdots \otimes \hom_{\mathcal{A}}(X_{k-1}, X_k) \to \hom_{\mathcal{A}}(X_0, X_k)[2-k]$$

1) Additive enlargement: we define the category  $\Sigma A$  to be the category whose objects are finite sums  $\bigoplus X_i[k_i], X_i \in \mathcal{A}, k_i \in \mathbb{Z}$  and whose maps are

(2) 
$$hom_{\Sigma \mathcal{A}}(\bigoplus_{i} X_{i}[k_{i}], \bigoplus_{j} Y_{j}[\ell_{j}]) = \bigoplus_{i,j} hom_{\mathcal{A}}(X_{i}, Y_{j})[\ell_{j} - k_{i}]$$

Note that we have induced multiplication maps

(3) 
$$m_k(a_k, \dots, a_1)^{ij} = \sum_{i_1, \dots, i_{k-1}} m_k(a_k^{i_{k-1}, j}, \dots, a_1^{i_1, j})$$

2) Twisted complexes: we define the category TwA to be the category whose objects are twisted complexes  $(X, \delta_X)$ ,

(4) 
$$X = \bigoplus_{i} X_{i}[k_{i}] \in \Sigma \mathcal{A}, \delta_{X} = (\delta_{X}^{ij}) \in \hom_{\Sigma \mathcal{A}}^{1}(X, X)$$

(i.e.  $\delta_X$  a degree 1 endomorphism) s.t.

- $\delta_X$  is strictly lower-triangular, and  $\sum_{k=1}^{\infty} m_k(\delta_x, \dots, \delta_x) = 0$ . It is a finite sum because  $\delta_X$  is lower triangular, and generalizes  $\delta_X \circ \delta_X = 0$ .

Example. For a simple map  $f: X_1 \to X_2, f \in \text{hom}_{\mathcal{A}}^1(X_1, X_2)$ , the condition is  $m_1(f) = 0$ . Now, for maps  $X_1[2] \xrightarrow{f} X_2[1] \xrightarrow{g} X_3$  and  $X_1[2] \xrightarrow{h} X_3$ ,

$$g \in \text{hom}^0(X_2, X_3) = \text{hom}^1(X_2[1], X_3)$$

(5) 
$$f \in \text{hom}^{0}(X_{1}[1], X_{2}[1]) = \text{hom}^{1}(X_{1}[2], X_{2}[1])$$
$$h \in \text{hom}^{-1}(X_{1}, X_{3}) = \text{hom}^{1}(X_{1}[2], X_{3})$$

the condition is  $m_1(f) = m_1(g) = 0$  and  $m_2(g, f) + m_1(h) = 0$ .

The morphisms in the category of twisted complexes are

(6) 
$$\hom_{\mathrm{Tw}\mathcal{A}}((X, \delta_X), (Y, \delta_Y)) = \hom_{\Sigma\mathcal{A}}(X, Y)$$

and

$$m_k^{\operatorname{Tw}\mathcal{A}}(a_k, \dots, a_1) = \sum_{i_0, \dots, i_k} \pm m_{k+i_0+\dots+i_k}^{\Sigma \mathcal{A}} \left( \underbrace{\delta_{X_k}, \dots, \delta_{X_k}}_{i_k}, a_k, \underbrace{\delta_{X_{k-1}}, \dots, \delta_{X_{k-1}}}_{i_{k-1}}, \dots, \underbrace{\delta_{X_1}, \dots, \delta_{X_1}}_{i_0}, a_1, \underbrace{\delta_{X_0}, \dots, \delta_{X_0}}_{i_0} \right)$$

$$(7)$$

Tw  $\mathcal{A}$  is a triangulated  $A_{\infty}$ -category, i.e. there are mapping cones satisfying the usual axioms.

Example. For  $a \in \text{hom}(X, Y)$ ,

(8) 
$$m_1^{\text{Tw}}(a) = m_1(a) \pm m_2(\delta_Y, a) \pm m_2(a, \delta_X) + \text{higher terms}$$

This is a generalization of being a chain map up to homotopy.

3) We now take the cohomology category  $D(\mathcal{A}) := H^0(\operatorname{Tw}\mathcal{A})$ , which is an honest triangulated category. The objects of the two categories are the same, but now our morphisms are  $\operatorname{hom}^{D(\mathcal{A})}(X,Y) := H^0(\operatorname{hom}^{\operatorname{Tw}\mathcal{A}}(X,Y), m_1^{\operatorname{Tw}(\mathcal{A})})$ . Note that  $\operatorname{hom}^{D(\mathcal{A})}(X,Y[k]) = H^k(\operatorname{hom}^{\operatorname{Tw}\mathcal{A}}(X,Y), m_1^{\operatorname{Tw}\mathcal{A}})$ . The composition is induced by  $m_2^{\operatorname{Tw}\mathcal{A}}$  on cohomology.

Remark. There is a variant of this called a split-closed derived category. Let  $\mathcal{A}$  be a linear category,  $X \in \mathcal{A}, p \in \text{hom}_{\mathcal{A}}(X, X)$  s.t.  $p^2 = p$  (idempotent). Define the image of p to be an object Y, and add maps  $u: X \to Y, v: Y \to X$  s.t.  $u \circ v = \text{id}_Y, v \circ u = p$ . That is, we enlarge  $\mathcal{A}$  to add these objects and maps, and define the split closure to be the category whose objects are (X, p) with p idempotent, and morphisms hom((X, p), (Y, p')) = p' hom(X, Y)p. This is more complicated in the  $A_{\infty}$  setting.

Geometrically, some exact triangles in DFuk(M) are given by Lagrangian connected sums (FOOO) and Dehn twists (Seidel).

• For an example of the latter, given a cylinder with a Lagrangian circle S, we can obtain a symplectomorphism  $\tau_S \in \operatorname{Symp}(M,\omega)$  which is the identity outside a neighborhood of S and, within that neighborhood, twists the cylinder around (in higher dimensions, define this using the geodesic flow in a neighborhood of  $S \cong T^*S$ ). If L is Lagrangian, then  $\tau_S(L)$  is Lagrangian as well. By Seidel, there exists an exact triangle in

DFuk(M):

(9) 
$$HF^*(S,L) \otimes S \xrightarrow{t} L$$
$$\tau_S(L)$$

These correspond to long exact sequences for HF(L', -).

- In the former situation, for  $L_1, L_2$  (graded) Lagrangians,  $L_1 \cap L_2 = \{p\}$  of index 0, we can construct the connected sum  $L_1 \#_p L_2$ , which looks locally like  $\tau_{L_1}(L_2)$  if  $L_1$  is a sphere and is given by  $\operatorname{Cone}(L_1 \stackrel{p}{\to} L_2)$  in general (consider this vs. " $L_1[1] \cup_p L_2 \simeq \operatorname{Cone}(L_1 \stackrel{0}{\to} L_2)$ "). For instance, in the torus  $T^2$ , consider two independent loops  $\alpha$  of degree 2 and  $\beta$  of degree 1, with two points of intersection p, q. Then  $\operatorname{Cone}(\alpha \stackrel{p+q}{\to} \beta) \simeq \gamma_1 \oplus \gamma_2$  is disconnected, where  $\gamma_1, \gamma_2$  are degree 1 loops. If we only started with  $\alpha, \beta$ , the triangulated envelope contains  $\gamma_1 \oplus \gamma_2$ , but not  $\gamma_1, \gamma_2$  separately. The split-closure does contain them.
- Now, if we start with two independent generators of the torus, successive Dehn twists give all the homotopy classes of loops in  $T^2$ , but each homotopy class contains infinitely many non-Hamiltonian isotopic Lagrangians. To generate  $D\operatorname{Fuk}(T^2)$  as a triangulated envelope, we need (for instance) one horizontal loop and infinitely many vertical loops. On the other hand,  $\alpha, \beta$  above are split generators. The key point is that  $\operatorname{Cone}(\alpha \xrightarrow{p+T^{q_q}} \beta)$  gives deformed loops, direct sums of which vary continuously within a homotopy class. But many cones and idempotents have no obvious geometric interpretation. For instance, the Clifford torus  $T = \{|x| = |y| = |z|\} \subset \mathbb{CP}^2$  has idempotents in HF(T,T) without any obvious geometric interpretation.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 19

## DENIS AUROUX

## 1. Homological Mirror Symmetry

Conjecture 1.  $X, X^{\vee}$  are mirror Calabi-Yau varieties  $\Leftrightarrow D^{\pi} \operatorname{Fuk}(X) \cong D^b \operatorname{Coh}(X^{\vee})$ 

Look at  $T^2$  at the level of homology [Polishchuk-Zaslow]: on the symplectic side,  $T^2 = \mathbb{R}^2/\mathbb{Z}^2$ ,  $\omega = \lambda dx \wedge dy$ , so  $\int_{T^2} \omega = \lambda$ . On the complex side,  $X^\vee = \mathbb{C}/\mathbb{Z} \oplus \tau \mathbb{Z}$ ,  $\tau = i\lambda$ . The Lagrangians L in X are Hamiltonian isotopic to straight lines with rational slope, and given a flat connection  $\nabla$  on a U(1)-bundle over L, we can arrange the connection 1-form to be constant. We will see that families of  $(L, \nabla)$  in the homology class (p, q) correspond to holomorphic vector bundles over  $X^\vee$  of rank p,  $c_1 = -q$ . For  $L \to X^\vee$  a line bundle, the pullback of L to the universal cover  $\mathbb{C}$  is holomorphically trivial, and

(1) 
$$L \cong \mathbb{C} \times \mathbb{C}/(z, v) \sim (z + 1, v), (z, v) \sim (z + \tau, \phi(z)v)$$
$$\phi \text{ holomorphic, } \phi(z + 1) = \phi(z)$$

Example.  $\phi(z) = e^{-2\pi i z} e^{-\pi i \tau}$  determines a degree 1 line bundle  $\mathcal{L}$  with a section given by the theta function

(2) 
$$\theta(\tau, z) = \sum_{m \in \mathbb{Z}} e^{2\pi i(\frac{\tau m^2}{2} + mz)}$$

More generally, set

(3) 
$$\theta[c', c''](\tau, z) = \sum_{m \in \mathbb{Z}} \exp\left(2\pi i \left[\frac{\tau(m + c')^2}{2} + (m + c')(z + c'')\right]\right)$$

Then

(4) 
$$\theta[c', c''](\tau, z + 1) = e^{2\pi i c'} \theta[c', c''](\tau, z) \\ \theta[c', c''](\tau, z + \tau) = e^{-\pi i \tau} e^{-2\pi i (z + c'')} \theta[c', c''](\tau, z)$$

since the interior of exp for the latter formula is

(5) 
$$\frac{\tau(m+c')^2}{2} + \tau(m+c') + (z+c'')(m+c') \\ = \frac{\tau(m+1+c')^2}{2} - \frac{\tau}{2} + (m+1+c')(z+c'') - (z+c'')$$

Furthermore, sections of  $\mathcal{L}^{\otimes n}$  are  $\theta[\frac{k}{n},0](n\tau,nz), k \in \mathbb{Z}/n\mathbb{Z}$ . By the above

(6) 
$$\theta[\frac{k}{n}, 0](n\tau, nz + n) = \theta[\frac{k}{n}, 0](n\tau, nz) \\ \theta[\frac{k}{n}, 0](n\tau, nz + n\tau) = e^{-\pi i n\tau} e^{-2\pi i nz} \theta[\frac{k}{n}, 0](n\tau, nz)$$

as desired. Other line bundles are given by pullback over the translation  $z \mapsto z + c''$ , and the higher rank bunddles are given by matrices or pushforward by finite covers.

On the mirror, consider the Lagrangian subvarieties

(7) 
$$L_0 = \{(x,0)\}, \nabla_0 = d \text{ (mirror to } \mathcal{O}),$$

$$L_n = \{(x,-nx)\}, \nabla_n = d \text{ (mirror to } \mathcal{L}^{\otimes n}),$$

$$L_n = \{(a,y)\}, \nabla_n = d + 2\pi i b dy \text{ ("mirror to } \mathcal{O}_Z, z = b + a\tau")}$$

For gradings, pick  $\arg(dz)|_{L_i} \in [-\frac{\pi}{2}, 0]$ . Then

(8) 
$$s_{k} = \left(\frac{k}{n}, 0\right) \in CF^{0}(L_{0}, L_{n}),$$

$$e = (a, -na) \in CF^{0}(L_{n}, L_{p}),$$

$$e_{0} = (a, 0) \in CF^{0}(L_{0}, L_{p})$$

We want to find the coefficient of  $e_0$  in  $m_2(e, s_0)$ , i.e. we need to count holomorphic disks in  $T^2$ . All these disks lift to the universal cover  $\mathbb{C}$ , and a Maslov index calculation gives that rigid holomorphic disks are immersed. We obtain an infinite sequence of triangles  $T_m$ ,  $m \in \mathbb{Z}$  in the universal cover.  $T_m$  has corners at (0,0), (a+m,-n(a+m)), (a+m,0), and the area is  $\int_{T_m} \omega = \frac{\lambda n(a+m)^2}{2}$ . Taking holonomy on  $\partial T_m$  gives

(9) 
$$\exp(2\pi i \int_{-n(a+m)}^{0} b dy) = \exp(2\pi i n(a+m)b)$$

The  $T_m$  are regular, and doing sign calculations makes them count positively. Now,

(10) 
$$m_2(e, s_0) = \left(\sum_{m \in \mathbb{Z}} T^{\lambda \frac{n}{2}(a+m)^2} e^{2\pi i n(a+m)b}\right) e_0$$

As usual, set  $T = e^{-2\pi}$  (convergence is not an issue here), i.e.  $T^{\lambda} = e^{2\pi i \tau}$ . Then

(11) 
$$\sum_{n \in \mathbb{Z}} \exp 2\pi i \left[ \frac{n\tau m^2}{2} + n(\tau a + b)m + (n\tau \frac{a^2}{2} + nab) \right]$$
$$= e^{\pi i n\tau a^2} e^{2\pi i nab} \theta(n\tau, n(\tau a + b))$$

What we have computed is the composition  $\mathcal{O} \xrightarrow{s_0} \mathcal{L}^n \xrightarrow{\operatorname{ev}_z} \mathcal{O}_z$ , where  $\operatorname{ev}_z$  is obtained by picking a trivialization of the fiber at z. Looking at the coefficient of  $e_0$  in  $m_2(e, s_k)$ , we obtain

$$\sum_{m \in \mathbb{Z}} \exp 2\pi i \left[ \frac{n\tau}{2} (a + m - \frac{k}{n})^2 + n(a + m - \frac{k}{n})b \right]$$

$$= \sum_{m \in \mathbb{Z}} \exp 2\pi i \left[ \frac{n\tau}{2} (m - \frac{k}{n})^2 + n(\tau a + b)(m - \frac{k}{n}) + \frac{n\tau}{2} a^2 + nab \right]$$

$$= e^{\pi i n \tau a^2} e^{2\pi i nab} \theta[0, \frac{k}{n}] (n\tau, n(\tau a + b))$$

so the ratios  $\frac{s_k}{s_0}$  match.

Next, we need to multiply sections. For  $s_0^{1\to 2} \in \text{hom}(L_1, L_2), s_0^{0\to 1} \in \text{hom}(L_0, L_1),$   $m_2(s_0^{1\to 2}, s_0^{0\to 1}) = c_0 s_0^{0\to 2} + c_1 s_1^{0\to 2} \text{ for } s_0^{0\to 2}, s_1^{0\to 2} \in \text{hom}(L_0, L_2) \text{ and}$ 

(13) 
$$c_0 = \sum_{n \in \mathbb{Z}} T^{n^2 \lambda} = \sum_{n \in \mathbb{Z}} e^{2\pi i \tau n^2}$$
$$c_1 = \sum_{n \in \mathbb{Z}} e^{2\pi i \tau (n + \frac{1}{2})^2}$$

This corresponds to  $\mathcal{O} \xrightarrow{\theta} \mathcal{L} \xrightarrow{\theta} \mathcal{L}^2$ .

(14) 
$$\theta(\tau, z)\theta(\tau, z) = \underbrace{\theta(2\tau, 0)}_{c_0} \underbrace{\theta(2\tau, 2z)}_{s_0} + \underbrace{\theta[\frac{1}{2}, 0](2\tau, 0)}_{c_1} \underbrace{\theta[\frac{1}{2}, 0](2\tau, 2z)}_{s_1}$$

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 20

## DENIS AUROUX

## 1. Homological Mirror Symmetry (CNTD.)

Last time, we studied homological mirror symmetry on  $T^2$  (with area form  $\lambda$ ) on the one hand and  $\mathbb{C}/\mathbb{Z} + \tau \mathbb{Z}, \tau = i\lambda$  on the other. Lagrangians of slope (p,q) with a U(1) flat connection correspond to vector bundles of rank p and degree -q (for (p,q)=(0,-1), this gives skyscraper sheaves). We showed that  $m_2$  corresponds to theta functions and to sections and products.

1.1. **Massey Products.** We consider these in the special case of a triangulated category  $\mathcal{D}$ , and consider objects and morphisms  $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \xrightarrow{h} X_4$  where  $g \circ f = 0, h \circ g = 0$ . Assume that  $hom(X_1, X_3[-1]) = hom(X_2, X_4[-1]) = 0$ . Then  $m_3(h, g, f) \in hom(X_1, X_4[-1])$ . Let K be s.t.  $K \to X_2 \xrightarrow{g} X_3 \xrightarrow{[1]} K[1]$  is a distinguished triangle (i.e. K[1] = Cone(g)). Then  $g \circ f = 0 \implies f$  factors through  $X_1 \xrightarrow{\overline{f}} K \to X_2$ , where  $\overline{f} \in hom(X_1, K)$  comes from

$$(1) \qquad \hom(X_1, X_3[-1]) \to \hom(X_1, K) \to \hom(X_1, X_2) \xrightarrow{g} \hom(X_1, X_3)$$

Similarly,  $h \circ g = 0 \implies h$  factors through  $X_3 \to K[1] \xrightarrow{\overline{h}} X_4$ , and we define

(2) 
$$m_3(h, g, f) := \overline{h}[-1] \circ \overline{f} : X_1 \xrightarrow{\overline{f}} K \xrightarrow{\overline{h}[-1]} X_4[-1]$$

Now, let's say that we had f, g, h in the  $A_{\infty}$  category of twisted complexes,  $K = \{X_2 \xrightarrow{g} X_3[-1]\},$ 

$$(3) X_1 \\ \downarrow f \\ X_2 \stackrel{g}{\longrightarrow} X_3[-1] \\ \downarrow h[-1] \\ X_4[-1]$$

and  $m_2^{\text{Tw}}(\overline{h}[-1], \overline{f}) = m_3(h, g, f)$ . If we add an extra step

$$e = X_{2} \xrightarrow{g} X_{3}[-1], m_{1}(e) = X_{1}$$

$$\downarrow 0 \qquad \qquad \downarrow f$$

$$X_{2} \xrightarrow{g} X_{3}[-1] \qquad X_{2} \xrightarrow{g} X_{3}[-1]$$

$$\downarrow M$$

$$X_{4}[-1]$$

then we get

(5) 
$$m_3(h, g, f) = m_3(h, m_1(e), f) = m_2(h, m_2(e, f)) + \text{ other terms which vanish}$$

Now, let  $\mathcal{L} \to X^{\vee}$  be a nontrivial degree 0 holomorphic line bundle over an elliptic curve, p, q generic points. Then the pairwise compositions in

(6) 
$$\mathcal{O} \xrightarrow{f} \mathcal{O}_p \xrightarrow{g} \mathcal{L}[1] \xrightarrow{h} \mathcal{O}_q[1]$$

vanish, and we have

(7) 
$$\operatorname{hom}(\mathcal{O}_p, \mathcal{L}[1]) = \operatorname{Ext}^1(\mathcal{O}_p, \mathcal{L}) \cong \operatorname{Hom}(\mathcal{L}, \mathcal{O}_p)^{\vee} \\ \operatorname{hom}(\mathcal{O}, \mathcal{L}[1]) = \operatorname{Ext}^1(\mathcal{O}, \mathcal{L}) \cong H^1(\mathcal{L}) = 0$$

Then  $K \cong \mathcal{L} \otimes \mathcal{O}(p)$  is a degree 1 line bundle, neither  $\mathcal{O}(p)$  nor  $\mathcal{O}(q)$ : note that  $\mathcal{O}(p)$  is a degree 1 line bundle with a section  $s_p, s_p^{-1}(0) = \{p\}$ . Then we have a long exact sequence

(8) 
$$0 \to \mathcal{L} \xrightarrow{s_p} \mathcal{L} \otimes \mathcal{O}(p) \to \mathcal{O}_p \to 0$$

giving us an exact triangle in the derived category

(9) 
$$K = \mathcal{L} \otimes \mathcal{O}(p) \to \mathcal{O}_p \xrightarrow{g} \mathcal{L}[1] \xrightarrow{[1]} K[1]$$

via our extension class. f should factor as a map from  $\mathcal{O}$  to K, and does via a nontrivial section  $\overline{f}$  of  $K = \mathcal{L} \otimes \mathcal{O}(p)$ . Moreover, for  $\overline{h}[-1]$  nontrivial in  $hom(K, \mathcal{O}_q)$ ,  $\overline{h}[-1] \circ \overline{f} \neq 0$ .

This matches with the calculation of  $m_3$  for the relevant Lagrangians in the Fukaya category of  $T^2$ : two horizontal lines and two vertical lines, bounding an infinite series of rectangles. See notes for a visual description of this.

## 2. Strominger-Yau-Zaslow (SYZ) Conjecture

Motivating question: how does one build a mirror  $X^{\vee}$  of a given Calabi-Yau X? Observe that homological mirror symmetry (1994) says that  $D^b\operatorname{Coh}(X^{\vee}) \cong D^{\pi}\operatorname{Fuk}(X)$ . Points  $p \in X^{\vee}$  correspond to skyscraper sheaves  $\mathcal{O}_p \in D^b\operatorname{Coh}(X^{\vee})$  and  $\mathcal{L}_p \in D^{\pi}\operatorname{Fuk}(X)$ . That is, we can regard  $X^{\vee}$  as the moduli space of skyscraper sheaves in  $D^b\operatorname{Coh}(X^{\vee})$  as well as a moduli space of certain objects of  $D^{\pi}\operatorname{Fuk}(X)$ . The question reduces to understanding exactly what are these certain objects. Four lectures ago, we computed  $\operatorname{Ext}^k(\mathcal{O}_p, \mathcal{O}_p) \cong \bigwedge^k V$  for V the tangent space at p. As a graded vector space,  $\operatorname{Ext}^*(\mathcal{O}_p, \mathcal{O}_p) \cong H^*(T^n; \mathbb{C})$ . Four lectures before that, we showd that  $HF^*(L, L)$  is in good cases isomorphic to  $H^*(L)$ , but if L bounds disks, these are only related by a spectral sequence.

Remark. Warning: recall that in general we are dealing with  $\Lambda$ -coefficients. In good cases, we can set  $T = e^{-2\pi}$  and hope that we have convergence. If convergence fails, we only get a formal family near LSCL.

If (optimistically) we assume  $\mathcal{L}_p$  is an actual Lagrangian, then it should be a Lagrangian torus. There are not enough of these: given  $T^n \cong L \subset X, V(L) \cong T^*L$ , one has that Lagrangian deformations of L are graphs of closed 1-forms, while Hamiltonian isotopies are graphs of exact 1-forms. Furthermore, for  $T^n$ ,  $\operatorname{Def}_L \cong H^1(L, \mathbb{R}) \simeq \mathbb{R}^n$ .

Now, recall the twisted Floer homology for pairs  $(L, \nabla)$ , with  $\nabla$  a flat U(1) connection on  $\underline{\mathbb{C}} \to L$ :  $\nabla = d + A, A \in \Omega^1(L, i\mathbb{R})$ . Taking this modulo gauge tranformations and exact 1-forms, we obtain  $H^1(L; i\mathbb{R})$ . One can hope that generic points of  $X^{\vee}$  parameterize isomorphism classes of  $(L, \nabla), L \subset X$  a Lagrangian torus and U(1) a flat connection.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 21

## DENIS AUROUX

## 1. SYZ Conjecture (cntd.)

Question: how does one build a mirror  $\check{X}$  of a given Calabi-Yau X? Recall that homological mirror symmetry says that  $D^b\mathrm{Coh}(\check{X})\cong D^\pi\mathrm{Fuk}(X)$ , and points  $p\in\check{X}$  correspond to skyscraper sheaves  $\mathcal{O}_p\in D^b\mathrm{Coh}(\check{X})$  and  $\mathcal{L}_p\in D^\pi\mathrm{Fuk}(X)$ . Regarding  $\check{X}$  as the moduli space of skyscraper sheaves in  $D^b\mathrm{Coh}(\check{X})$  as well as a moduli space of certain objects of  $D^\pi\mathrm{Fuk}(X)$ , the question reduces to understanding exactly what are these certain objects. Recall that  $HF^*(\mathcal{L}_p,\mathcal{L}_p)\cong \mathrm{Ext}^*(\mathcal{O}_p,\mathcal{O}_p)=H^*(T^n,\mathbb{C})$ .

**Conjecture 1.** Generic points of  $\check{X}$  parameterize isomorphism classes of  $(L, \nabla)$ ,  $L \subset X$  a Lagrangian torus and  $\nabla$  a flat U(1)-connection on  $\underline{\mathbb{C}} \to L$  (corresponding to elements of  $\operatorname{Hom}(\pi_1 L, U(1))$ ).

**Definition 1.** A special Lagrangian submanifold is one with Im  $(\Omega|_L) = 0$ .

Conjecture 2 (SYZ). X, X carry dual fibrations by special Lagrangian tori

(1) 
$$T^{n} \xrightarrow{X} \check{T}^{n} \xrightarrow{X} \check{T} = \operatorname{Hom}(\pi_{1}T, U(1))$$

$$\downarrow^{\pi} \qquad \qquad \downarrow^{\pi^{\vee}}$$

$$B \qquad B$$

i.e.  $\check{X} = \{(L, \nabla), L \text{ fiber of } \pi, \nabla \in \text{hom}(\pi_1 T, U(1))\}.$ 

Remark. Warnings: constructing special Lagrangian fibrations is hard/impossible (..., Joyce,..., Haase-Zharkov, Gross-Siebert,...). They should come from LCSL degenerations, and different LSCL degenerations give different special Lagrangian fibrations and thus different mirrors. Furthermore, special Lagrangian fibrations will typically have singular fibers, so the dual fibration is not well defined. The issue here is "instanton corrections".

1.1. **Special Lagrangian submanifoldds.** Let  $(X, \omega, J)$  be a Kähler manifold,  $g = \omega(\cdot, J \cdot)$  the Kähler metric,  $\Omega \in \Omega^{n,0}$  a holomorphic volume form. It is *strictly Calabi-Yau* if g is Ricci-flat, i.e.  $|\Omega|_g$  is constant, or  $\Omega \wedge \overline{\Omega} = c(n)\omega^n$ , or  $\nabla \Omega = 0$ , or  $\text{hol}_g \subseteq SU(n)$ . It is *almost Calabi-Yau* if  $|\Omega|_g = \psi \in C^{\infty}(X, \mathbb{R}_+), \Omega \wedge \overline{\Omega} = c(n)\psi^2\omega^n$ .

**Proposition 1.** If  $L \subset X$  is Lagrangian,  $\Omega|_L \in \Omega^n(L,\mathbb{C})$  is  $e^{i\phi}\psi \operatorname{vol}_g|_L$  with  $e^{i\phi}: L \to S^1$  is a phase function.

*Proof.* Linear algebra! At  $p \in L$ ,  $(T_pX, \omega_p, J_p, T_pL) \cong (\mathbb{C}^n, \omega_0, J_0, \mathbb{R}^n)$ , and

(2) 
$$\Omega_p|_{\mathbb{R}^n} = e^{i\phi(p)}\psi(p)dz_1 \wedge \dots \wedge dz_n|_{\mathbb{R}^n} = e^{i\phi}\psi dx_1 \wedge \dots \wedge dx_n$$

We say that L is special if if  $e^{i\phi}: L \to S^1$  is constant. Then  $\int_L \Omega \in e^{i\phi} \mathbb{R}_+$ . Given  $[L] \in H_n(X)$ , we normalize  $\Omega$  s.t.  $\int_L \Omega = 1, \int_L \Omega \in \mathbb{R}_+$ . Then this definition of specialness is equivalent to our previous one, i.e. Im  $\Omega|_L = 0$ , and  $\operatorname{Re} \Omega|_L = \psi \operatorname{vol}_q|_L$ .

Remark. In the case of strictly Calabi-Yau manifolds, special Lagrangians are calibrated and hence absolutely volume-minimizing in their homology class. For any n-plane  $\Pi$ , Re  $\Omega|_{\Pi} \leq \text{vol}_q|_{\Pi}$ , with equality iff  $\Pi$  is special Lagrangian. Thus,

(3) 
$$[\operatorname{Re}\Omega] \cdot [L] = \int_{L} \operatorname{Re}\Omega \leq \int_{L} \operatorname{vol}_{g} = \operatorname{vol}(L)$$

with equality again if L is special Lagrangian.

Remark. Since  $c_1(TX) = 0$ ,  $\exists$  a global  $\mathbb{Z}$ -cover of the Lagrangian Grasmannian of X. We can describe a graded Lagrangian plane as a Lagrangian plane  $\Pi \subset TX$  equipped with a real lift  $\phi \in \mathbb{R}$  of the phase. For an oriented Lagrangian submanifold  $L \subset X$ ,  $e^{i\phi}: L \to S^1$  might not lift to  $\phi: L \to \mathbb{R}$ , and the obstruction is a homotopy class in  $[L, S^1] = H^1(L, \mathbb{Z})$ : up to a factor of 2, this is the Maslov class  $\mu_L$ . For L a special Lagrangian,  $\mu_L = 0$ , graded lifts exists, and HF can be  $\mathbb{Z}$ -graded.

1.2. **Deformations of special Lagrangians.** Let  $v \in C^{\infty}(NL)$  be a normal vector field,  $\phi_t = \exp(tv), L_t = \phi_t(L)$ . One may ask when  $L_t$  is special Lagrangian. It is Lagrangian if  $\omega|_{L_t} = 0$ , i.e.  $\phi_t^* \omega = 0$ . To first order,

(4) 
$$\frac{d}{dt}(\phi_t^*\omega)|_{t=0} = (L_v\omega)|_L = (d\iota_v\omega)|_L$$

so  $\beta = -\iota_v \omega \in \Omega^1(L, \mathbb{R})$  should be closed. For specialness, need Im  $\Omega|_{L_t} = 0$ , i.e.  $\phi_t^*(\operatorname{Im} \Omega) = 0$ . Again, to first order,

(5) 
$$\frac{d}{dt}(\phi_t^* \operatorname{Im} \omega)|_{t=0} = (L_V \operatorname{Im} \Omega)|_L = (d\iota_v \operatorname{Im} \Omega)|_L$$

and  $\tilde{\beta} = \iota_v \text{Im } \Omega \in \Omega^{n-1}(L, \mathbb{R})$  should be closed.

Now, in the standard metric on  $T_pL \cong \mathbb{R}^n \subset \mathbb{C}^n \cong T_pX$ ,  $\Omega_p = \psi dz_1 \wedge \cdots \wedge dz_n$ . Setting  $v = \sum a_i \frac{\partial}{\partial y_i}$  gives  $\beta = -\iota_v \omega_0 = \sum a_i dx_i$ ,

(6) 
$$\tilde{\beta} = \iota_v \operatorname{Im} \Omega|_L = \sum a_i (-1)^{i-1} \psi dx_1 \wedge \dots \wedge \widehat{dx_i} \wedge \dots \wedge dx_n = \psi \cdot *\beta$$

In the strict Calabi-Yau case,  $\tilde{\beta} = *\beta$  so  $d\beta = d\tilde{\beta} = 0 \Leftrightarrow \beta$  is harmonic.

**Proposition 2.** First order deformations of special Lagrangian L in a strict (resp. almost) Calabi-Yau manifold are given by  $\mathcal{H}^1(L,\mathbb{R})$  (resp.  $\mathcal{H}^1_{\psi}(L,\mathbb{R})$ ), where

(7) 
$$H^{1}_{\psi}(L,\mathbb{R}) = \{ \beta \in \Omega^{1}(L,\mathbb{R}) \mid d\beta = 0, d^{*}(\psi\beta) = 0 \}$$

It is still true that  $\mathcal{H}^1_{\psi}(L,\mathbb{R}) \cong H^1(L,\mathbb{R})$ .

The idea is to redo the Hodge decomposition theorem with

(8) 
$$\Omega^1 \stackrel{(d,\psi^{-1}d^*\psi)}{\to} \Omega^0 \oplus \Omega^2$$

Or, if  $n \neq 2$ ,  $\psi$ -harmonicity for g is equivalent to harmonicity for  $\psi^{\frac{2}{n-2}}g$ .

**Theorem 1** (McLean, Joyce). Deformations of special Lagrangians are unobstructed, i.e. the moduli space of special Lagrangians is a smooth manifold B with  $T_LB \cong \mathcal{H}^1_{\psi}(L,\mathbb{R}) \cong H^1(L,\mathbb{R})$ .

*Proof.* Locally near L, deformations correspond to normal vector fields via the exponential map. Consider the Banach bundle  $\mathcal{E} \to U \subset W^{k,p}(L,NL)$  with fiber at v given by

(9) 
$$\mathcal{E}_v = W^{k-1,p}(L, \bigwedge^2(T^*L)) \oplus W^{k-1,p}(L, \bigwedge^n T^*L)$$

We have a section of  $\mathcal{E}$  given by

(10) 
$$s = (\exp(v)^* \omega, \exp(v)^* \operatorname{Im} \Omega)$$

which is closed, and even exact. Then  $B = s^{-1}(0)$ . Let  $\mathcal{F}\{\mathcal{E}\}$  be the Banach subbundle of exact forms. Then s is a Fredholm section of  $\mathcal{F}$ . Let  $\omega^{\#}: NL \xrightarrow{\sim} T^*L$  be the map  $v \mapsto -\iota_v \omega$ , we have that

(11) 
$$ds(0) \circ (\omega^{\#})^{-1} : \beta \mapsto (-d\beta, d(\psi \cdot *\beta))$$

is surjective and  $s^{-1}(0)$  is smooth.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 22

## DENIS AUROUX

## 1. SYZ Conjecture (cntd.)

Recall:

**Proposition 1.** First order deformations of special Lagrangian L in a strict (resp. almost) Calabi-Yau manifold are given by  $\mathcal{H}^1(L,\mathbb{R})$  (resp.  $\mathcal{H}^1_{\psi}(L,\mathbb{R})$ ), where

(1) 
$$H^1_{\psi}(L,\mathbb{R}) = \{ \beta \in \Omega^1(L,\mathbb{R}) \mid d\beta = 0, d^*(\psi\beta) = 0 \}$$

It is still true that  $\mathcal{H}^1_{\psi}(L,\mathbb{R}) \cong H^1(L,\mathbb{R})$ .

**Theorem 1** (McLean, Joyce). Deformations of special Lagrangians are unobstructed, i.e. the moduli space of special Lagrangians is a smooth manifold B with  $T_LB \cong \mathcal{H}^1_{\psi}(L,\mathbb{R}) \cong H^1(L,\mathbb{R})$ .

There are two canonical isomorphisms  $T_L B \xrightarrow{\sim} H^1(L, \mathbb{R}), v \mapsto [-\iota_v \omega]$  ("symplectic") and  $T_L B \xrightarrow{\sim} H^{n-1}(L, \mathbb{R}), v \mapsto [\iota_v \operatorname{Im} \Omega]$  "complex".

**Definition 1.** An affine structure on a manifold N is a set of coordinate charts with transition functions in  $GL(n, \mathbb{Z}) \ltimes \mathbb{R}^n$ .

Corollary 1. B carries two affine structures.

For affine manifolds, mirror symmetry exchanges the two affine structures. Our particular case of interest is that of special Lagrangian tori, so dim  $H^1 = n$ . The usual harmonic 1-forms on flat  $T^n$  have no zeroes, and give a pointwise basis of  $T^*L$ . We will make a standing assumptions that  $\psi$ -harmonic 1-forms for  $g|_L$  have no zeroes (at least ok for  $n \leq 2$ ). Then a neighborhood of L is fibered by special Lagrangian deformations of L: locally,

(2) 
$$T^{n} \longrightarrow U \subset X$$

$$\downarrow^{\pi}$$

$$V \subset B$$

In local affine coordinates, we pick a basis  $\gamma_1, \ldots, \gamma_n \in H_1(L, \mathbb{Z})$ : deforming from L to L', the deformation of  $\gamma_i$  gives a cylinder  $\Gamma_i$ , and we set  $x_i = \int_{\Gamma_i} \omega$  (the flux of the deformation  $L \to L'$ ). These are affine coordinates on the symplectic

side. On the complex side, pick a basis  $\gamma_1^*, \ldots, \gamma_n^* \in H_{n-1}(L, \mathbb{Z})$ , construct the associated  $\Gamma_i^*$ , and set  $x_i^* = \int_{\Gamma_i^*} \operatorname{Im} \Omega$ . Globally, there is a monodromy  $\pi_1(B, *) \to \operatorname{Aut} H^*(L, \mathbb{Z})$ . In our case, the monodromies in  $GL(H^1(L, \mathbb{Z})), GL(H^{n-1}(L, \mathbb{Z}))$  are transposes of each other.

1.1. Prototype construction of a mirror pair. Let B be an affine manifold,  $\Lambda \subset TB$  the lattice of integer vectors. Then  $TB/\Lambda$  is a torus bundle over B, and carries a natural complex structure, e.g.

(3) 
$$T(\mathbb{R}^n) \cong \mathbb{C}^n, \mathbb{C}^n = \mathbb{R}^n \oplus \mathbb{R}^n, GL(n, \mathbb{Z}) \ni A \mapsto \begin{pmatrix} A & 0 \\ 0 & A \end{pmatrix}$$

Setting  $\Lambda^* = \{ p \in T^*B \mid p(\Lambda) \subset \mathbb{Z} \}$  to be the dual lattice of integer covectors, we find that  $T^*B/\Lambda^*$  has a natural symplectic structure since  $GL(n,\mathbb{Z}) \ni A \mapsto \begin{pmatrix} A & 0 \\ 0 & A^T \end{pmatrix} \in \operatorname{Sp}(2n)$ .

In our case, we have two affine structures with dual monodromies

$$TB \xrightarrow{\sim} T^*B$$

$$\sim \downarrow^{cx} \qquad \qquad symp \downarrow \sim$$

$$H^{n-1}(L, \mathbb{R}) \xrightarrow{\sim} H_1(L, \mathbb{R})$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$\Lambda_c = H^{n-1}(L, \mathbb{Z}) \xrightarrow{\sim} H_1(L, \mathbb{Z}) = \Lambda_c^*$$

so the complex manifold  $TB/\Lambda_c$  is diffeomorphic to the symplectic manifold  $T^*B/\Lambda_s^*$ . Dually,  $X^{\vee} \cong T^*B/\Lambda_c^* \cong TB/\Lambda_s$ .

## 1.2. More explicit constructions [cf. Hitchin]. Let

(5) 
$$M = \{(L, \nabla) \mid L \text{ a special Lagrangian torus in } X,$$
$$\nabla \text{ flat } U(1) - \text{conn on } \mathbb{C} \times L \text{ mod gauge} \}$$

i.e.  $\nabla = d + iA, iA \in \Omega^1(L, i\mathbb{R}), dA = 0$  mod exact forms.

(6)  

$$T_{(L,\nabla)}M = \{(v, i\alpha) \in C^{\infty}(NL) \oplus \Omega^{1}(L; i\mathbb{R}) \mid -\iota_{v}\omega \in \mathcal{H}^{1}_{\psi}(L, \mathbb{R}), d\alpha = 0 \text{ mod Im } (d)\}$$

$$= \{(v, i\alpha) \in C^{\infty}(NL) \oplus \Omega^{1}(L; i\mathbb{R}) \mid -\iota_{v}\omega + i\alpha \in \mathcal{H}^{1}_{\psi}(L; \mathbb{C})\}$$

$$= H^{1}_{\psi}(L, \mathbb{C})$$

which is a complex vector space, and  $J^{\vee}$  is an almost-complex structure.

**Proposition 2.**  $J^{\vee}$  is integrable.

*Proof.* We build local holomorphic coordinates. Let  $\gamma_1, \ldots, \gamma_n$  be a basis of  $H_1(L, \mathbb{Z})$ , and assume  $\gamma_i = \partial \beta_i, \beta_i \in H_2(X, L)$ . Set

(7) 
$$z_i(L, \nabla) = \underbrace{\exp(-\int_{\beta_i} \omega)}_{\mathbb{R}_+} \underbrace{\operatorname{hol}_{\nabla}(\gamma_i)}_{U(1)} \in \mathbb{C}^*$$

Then

(8) 
$$\operatorname{dlog} z_i : (v, i\alpha) \mapsto -\int_{\gamma_i} \iota_v \omega + \int_{\gamma_i} i\alpha = \langle \underbrace{[-\iota_v \omega + i\alpha]}_{H^1(L, \mathbb{C})}, \gamma_i \rangle$$

is  $\mathbb{C}$ -linear. If there are no such  $\beta_i$ , we instead use a deformation tube as constructed earlier. Warning: all of our formulas are up to (i.e. may be missing) a factor of  $2\pi$ .

Next, consider the holomorphic (n,0)-form on M

$$(9) \quad \Omega^{\vee}((v_1, i\alpha_1), \dots, (v_n, i\alpha_n)) = \int_L (-\iota_{v_1}\omega + i\alpha_1) \wedge \dots \wedge (-\iota_{v_n}\omega + i\alpha_n)$$

After normalizing  $\int_L \Omega = 1$ , we have a Kähler form

(10) 
$$\omega^{\vee}((v_1, i\alpha_1), (v_2, i\alpha_2)) = \int_L \alpha_2 \wedge (\iota_{v_1} \operatorname{Im} \Omega) - \alpha_1 \wedge (\iota_{v_2} \operatorname{Im} \Omega)$$

**Proposition 3.**  $\omega^{\vee}$  is a Kähler form compatible with  $J^{\vee}$ .

*Proof.* Pick a basis  $[\gamma_i]$  of  $H_{n-1}(L,\mathbb{Z})$  with a dual basis  $[e_i]$  of  $H_1(L,\mathbb{Z})$ , i.e.  $e_i \cap \gamma_i = \delta_{ij}$ . For all  $a \in H^1(L), b \in H^{n-1}(L)$ 

(11) 
$$()\langle a \cup b, [L] \rangle = \sum_{i} \langle a, e_i \rangle \langle b, \gamma_i \rangle$$

Letting  $a = \sum a_i dx_i$ ,  $b = \sum b_i (-1)^{i-1} (dx_1 \wedge \cdots \wedge \widehat{dx_i} \wedge \cdots \wedge dx_n)$ ,  $\int_{T^n} a \wedge b = \sum a_i b_i$ . Again, take a deformation from  $L_0$  to L',  $C_i$  the tube (an n-chain) formed by the deformation of  $\gamma_i$ , and set  $p_i = \int_{C_i} \text{Im } \Omega$ ,  $\theta_i = \int_{e_i} A$  for A the connection 1-form (i.e.  $\text{hol}_{e_i}(\nabla) = \exp(i\theta_i)$ ). Then

(12) 
$$dp_i : (v, i\alpha) \mapsto \int_{\gamma_i} \iota_v \operatorname{Im} \Omega = \langle [\iota_v \operatorname{Im} \Omega], \gamma_i \rangle$$
$$d\theta_i : (v, i\alpha) \mapsto \int_{e_i} \alpha = \langle [\alpha], e_i \rangle$$

By (11),  $\omega^{\vee} = \sum dp_i \wedge d\theta_i$ , implying that  $\omega^{\vee}$  is closed, and

(13) 
$$\omega^{\vee}((v_{1},\alpha_{1}),(v_{2},\alpha_{2})) = \int_{L} \alpha_{2} \wedge (-\psi *_{g} \iota_{v_{1}}\omega) - \alpha_{1} \wedge (-\psi *_{g} \iota_{v_{2}}\omega)$$

$$= \int_{L} \psi \cdot (\langle \alpha_{1},\iota_{v_{2}}\omega \rangle_{g} - \langle \alpha_{2},\iota_{v_{1}}\omega \rangle_{g}) \operatorname{vol}_{g}$$

$$\omega^{\vee}((v_{1},\alpha_{1}),J^{\vee}(v_{2},\alpha_{2})) = \int_{L} \psi \cdot (\langle \alpha_{1},\alpha_{2}\rangle_{g} + \langle \iota_{v}\omega,\iota_{v_{2}}\omega \rangle_{g}) \operatorname{vol}_{g}$$

which is clearly a Riemannian metric.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 23

## DENIS AUROUX

Recall that given an (almost) Calabi-Yau manifold  $(X, J, \omega, \Omega)$ , we defined M to be the set of pairs  $(L, \nabla)$ ,  $L \subset X$  a special Lagrangian torus,  $\nabla$  a flat U(1) connection on  $\mathbb{C} \times L$  modulo gauge equivalence. Up to  $2\pi$ ,

(1) 
$$T_{(L,\nabla)}M = \{(v, i\alpha) \in C^{\infty}(NL) \oplus \Omega^{1}(L; i\mathbb{R}) \mid -\iota_{v}\omega + \frac{1}{2\pi}i\alpha \in \mathcal{H}^{1}_{\psi}(L; \mathbb{C})\}$$
$$= H^{1}_{\psi}(L, \mathbb{C}) = \{\beta \in \Omega^{1}(L, \mathbb{R}) \mid d\beta = 0, d^{*}(\psi\beta) = 0\}, \psi = |\Omega|_{q}$$

is a complex vector space, giving us an integrable  $J^{\vee}$  on M with holomorphic local coordinates

(2) 
$$z_{\beta}(L, \nabla) = \underbrace{\exp(-2\pi\omega(\beta))}_{\mathbb{R}_{+}} \underbrace{\operatorname{hol}_{\nabla}(\gamma)}_{U(1)} \in \mathbb{C}^{*}$$

and a holomorphic (n, 0)-form

$$(3) \quad \Omega^{\vee}((v_1, i\alpha_1), \dots, (v_n, i\alpha_n)) = i^{-n} \int_L (-\iota_{v_1}\omega + \frac{i\alpha_1}{2\pi}) \wedge \dots \wedge (-\iota_{v_n}\omega + \frac{i\alpha_n}{2\pi})$$

After normalizing  $\int_L \Omega = 1$ , we obtained a compatible Kähler form

(4) 
$$\omega^{\vee}((v_1, i\alpha_1), (v_2, i\alpha_2)) = \frac{1}{2\pi} \int_L \alpha_2 \wedge (\iota_{v_1} \operatorname{Im} \Omega) - \alpha_1 \wedge (\iota_{v_2} \operatorname{Im} \Omega)$$

Now, let B be the set of special Lagrangian tori,  $\pi^{\vee}: M \to B, (L, \nabla) \to L$  a special Lagrangian torus fibration (with torus fiber  $\{(0, i\alpha)\}$ ) "dual to  $\pi: X \to B$ ". Note that  $\pi^{\vee}$  has a zero section  $\{(L, d)\}$  which is a special Lagrangian, and has complex conjugation  $(L, \nabla) \leftrightarrow (L, \nabla^*)$ .

Example. As usual, let  $T^2 = \mathbb{C}/\mathbb{Z} + i\rho\mathbb{Z}$ ,  $\Omega = dz$ ,  $\omega = \frac{\lambda}{\rho}dx \wedge dy$ ,  $\int_{T^2}\omega = \lambda$ . L is special Lagrangian  $\Leftrightarrow$  Im  $dz_|L = 0 \Leftrightarrow L$  is parallel to the real axis. We have a fibration  $T^2 \stackrel{\pi}{\to} S^1 = \mathbb{R}/\rho\mathbb{Z}$ ,  $(x,y) \mapsto y$ , with fibers  $L_t = \{y = t\}$ , inducing a complex affine structure with affine coordinate  $y \in \mathbb{Z}$  Im  $\Omega$  on the arc from  $L_0$  to L), size( $S^1$ ) =  $\rho$ , and a symplectic affine structure  $\frac{\lambda}{\rho}y$  (= the symplectic area swept), size( $S^1$ ) =  $\lambda$ . On the mirror  $M = \{(L, \nabla)\} \in \mathbb{R}/\rho\mathbb{Z}$ , the holomorphic coordinate for  $J^\vee$  is  $\exp(-2\pi\frac{\lambda}{\rho}y)e^{i\theta}$ ,  $\theta \in \mathbb{R}/2\pi\mathbb{Z}$ ,  $\nabla = d + i\theta dx$ . Or, taking  $\frac{1}{2\pi i}\log$ ),  $z^\vee = \frac{\theta}{2\pi} + i\frac{\lambda}{\rho}y \in \mathbb{C}/\mathbb{Z} + i\lambda\mathbb{Z}$ . Furthermore  $\Omega^\vee = dz^\vee$ ,  $\omega^\vee = \frac{1}{2\pi}d\theta \wedge dy$ . Our SYZ transformation exchanges Lagrangian sections of  $\pi$  and flat connections with a connection on a holomorphic line bundle. Explicitly, set  $L = \{x = f(y)\}$ , f:

 $\mathbb{R}/\rho\mathbb{Z} \to \mathbb{R}/\mathbb{Z}$ , with flat connection  $\nabla = d + ih(y)dy$ ,  $h: \mathbb{R}/\rho\mathbb{Z} \to \mathbb{R}$ . We build a Hermitian connection  $\nabla = d + i f(y) d\theta + i h(y) dy$  on a locally trivialized Hermitian line bundle  $\mathcal{L}$ . Note that changing the trivialization by  $e^{i\theta}$  changes the connection form by  $id\theta$ , i.e.  $f \leftrightarrow f+1$ , glue y=0 to  $y=\rho$  by  $e^{i\deg(f)\theta}$ . Furthermore,  $\deg (\mathcal{L}) = \deg (f: S^1 \to S^1)$ . We have a holomorphic structure  $\overline{\partial}^{\nabla} = \check{\nabla}^{0,1}$ .

In higher-dimensional tori, we have  $L = \{x = f(y)\}$  Lagrangian,  $f: \mathbb{R}^n/\Lambda \to$  $\mathbb{R}^n/\mathbb{Z}^n$ ,  $\nabla = d + i\sum_j h_j(y)dy_j$ ,  $h: \mathbb{R}^n/\Lambda \to \mathbb{R}^n$  on the one side,  $\check{\nabla} = d + i\sum_j h_j(y)dy_j$  $i\sum_{j}f_{j}(y)d\theta_{j}+i\sum_{j}h_{j}(y)dy_{j}$ , which is holomorphic  $\Leftrightarrow$  the curvature is  $(1,1)/J^{\vee}$ . Set

(5) 
$$F = i \sum_{j,k} \frac{\partial f_j}{\partial y_k} dy_k \wedge d\theta_j + i \sum_{j,k} \frac{\partial h_j}{\partial y_k} dy_k \wedge dy_j$$

Then  $J^{\vee}$  exchanges  $dy_k$  and  $d\theta_k$  up to canonical scaling, and is holomorphic  $\Leftrightarrow$ 

- $\frac{\partial f_j}{\partial y_k} = \frac{\partial f_k}{\partial y_j}$  for  $\sum f_j dy_j$  a closed 1-form on  $\mathbb{R}^n/\Lambda$  ( $\Leftrightarrow L$  Lagrangian),  $\frac{\partial h_j}{\partial y_k} = \frac{\partial h_k}{\partial y_j}$  for  $\sum h_j dy_j$  a closed 1-form ( $\Leftrightarrow \nabla$  is flat).

Example. Let X be a K3 surface, namely a simply connected complex surface with  $K_X \cong \mathcal{O}_X$ , e.g. a 4-dimensional hypersurface  $\{P_4(x_0,\ldots,x_3)=0\}\subset \mathbb{CP}^3$ for  $P_4$  a homogeneous polynomial in degree 4, or a double cover of  $\mathbb{CP}^1 \times \mathbb{CP}^1$ ,  $\{z^2 = P_{4,4}((x_0, x_1), (y_0, y_1))\} \subset \text{Tot}(\mathcal{O}(2, 2))$  with Hodge diamond

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

Any K3 surface is hyperkähler, i.e. there are three complex structures I, J, K =IJ = -JI inducing three Kähler forms  $\omega_I, \omega_J, \omega_K$  for the same Kähler metric g. The idea is the following: given  $I, [\omega_I], \text{ Yau's theorem gives a Ricci-flat Kähler}$ metric g, and we obtain a holomorphic volume form  $\Omega_I \in \Omega^{2,0}$  with  $|\Omega_I|_q =$  $1, \Omega_U = \omega_J + i\omega_K$ , where  $\omega_I$  is (1,1) for  $I, \omega_J = \text{Re } \Omega_I, \omega_K = \text{Im } \Omega_I (2,0) + (0,2)$ for I are pointwise orthonormal self-dual 2-forms which are covariantly constant.

Some (not all) K3 surfaces admit fibrations by elliptic curves over spheres, typically with 24 nodal singular fibers. For instance, given a double coordinate of  $\mathbb{CP}^1 \times \mathbb{CP}^1$ , we project to a  $\mathbb{CP}^1$  factor, and observe that the fibers are double covers of  $\mathbb{CP}^1$  branched at four points. Now, assume we have one of these with a holomorphic section. The fibers will be I-complex curves, and thus special Lagrangian for  $(\omega_J, \Omega_J = w_K + i\omega_I)$ ,  $(\omega_K, \Omega_K = \omega_I + i\omega_J)$  (they are calibrated by  $\omega_I$ , which is (1,1) for I so  $\omega_J, \omega_K$  vanish). Mirror symmetry corresponds these latter two structures.

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 24

## DENIS AUROUX

0.1. General Approach to Special Lagrangian Fibrations. The idea is to degenerate X to a union of toric varieties, build a degenerate fibration there, and try to smooth it: the approach is due to Haase-Zharkov, WD Ruan, Gross-Siebert, etc. This is a special type of LCSL. We first sketch this in the K3 case: as last time,

(1) 
$$X_{\lambda} = \{ P_{\lambda} = x_0 x_1 x_2 x_3 + \lambda P_4(x_0 : \dots : x_3) = 0 \} \subset \mathbb{CP}^3$$

with  $\omega_{\lambda} = \omega_{\mathbb{CP}^3}|_{X_{\lambda}}$ ,  $\Omega_{\lambda} = \operatorname{res}_{X_{\lambda}}(\frac{dx_1dx_2dx_3}{P_{\lambda}})$ . As  $\lambda \to 0$ , this degenerates to  $X_0$ , a union of 4  $\mathbb{CP}^2$ s, with  $\omega_0$  the standard form on each component and  $\Omega_0 = \prod \frac{dx_i}{x_i}$ . Now, we find that  $\{|x_i| = \text{constants}\}$  are special Lagrangian (looking at  $T^2 \subset \mathbb{CP}^2$ ), but they degenerate to  $S^1$  at the edges and points at the vertices.

We would like to smooth this for  $\lambda \neq 0$  small. The model in dimension 1 is as follows: we smooth  $\{xy=0\} \subset \mathbb{C}^2$  to  $\{xy=\lambda\}$ , and  $\Omega = \frac{dx}{x} = -\frac{dy}{y}$  gives that |x| = const, |y| = const are special Lagrangian tori. In dimension one higher, we model along the edge (|z| = const gives  $S_z^1$  times this model) except that we perturb xy=0 to  $xy+\lambda P_4(z)=0$ . The four roots of  $P_4$  give 4 singularities of the  $T^2$  fibration on each edge of the torus, giving  $S^2$  an affine structure on  $S^2 \setminus \{24 \text{ points}\}$ . This same procedure holds in greater generality, and gives affine structures and a way of building a candidate mirror (Gross-Siebert). However, it is not clear if the affine manifold built this way is the base of a special Lagrangian fibration (probably not, according to [Joyce]).

0.2. Landau-Ginzburg models and non-Calabi Yau manifolds. Our motivating example is the mirror symmetry between  $\mathbb{CP}^1$  and  $(\mathbb{C}^*, W = z + \frac{1}{z})$ . A Landau-Ginzburg model is a noncompact Kähler manifold and a holomorphic function W (the "superpotential"), which measures the obstruction to being Calabi-Yau and affects the geometric interpretation of mirror symmetry. The general idea is that the geometry of X corresponds to the geometry of the critical points of W in  $X^{\vee}$ .

Returning to our example, we start with  $\mathbb{C}^*$  with any  $\omega$ ,  $\Omega = \frac{dz}{z}$  (an open Calabi Yau): we have a special Lagrangian fibration by circles  $S^1(r) = \{|z| = r\}$  with base  $\mathbb{R}$ . Dualizing gives back  $\mathbb{C}^*$ , and mirror symmetry works well as in SYZ (e.g.  $HF(L_p, L_p) \cong H^*(S^1, \mathbb{C}) \cong \operatorname{Ext}^*(\mathcal{O}_p, \mathcal{O}_p)$ ). However, we need to

incorporate the noncompact Lagrangians [Seidel's "wrapped Fukaya category": we perturb by a rotation at  $\infty$ , obtaining  $HW^*(L_0, L_0) \cong \mathbb{C}[t^{\pm 1}] \cong \text{Hom}(\mathcal{O}, \mathcal{O})$  (holomorphic functions over  $\mathbb{C}^*$ )].

Now we look at  $\mathbb{CP}^1 = \mathbb{C}^* \cup \{0, \infty\}$ , with standard  $\omega$ ,  $\Omega = \frac{dz}{z}$  (with poles at 0 and  $\infty$ ). We can still consider a family of special Lagrangian circles, but typically  $HF^*(L,L) = 0$  gives the zero object in the bounded derived Fukaya category. Furthermore, the Floer homology is obstructed, as the circles bound disks: recall that, when L, L' bound disks,  $\partial$  on CF(L, L') squares to  $\partial^2(a) = m'_0 \cdot a - a \cdot m_0$ ,

(2) 
$$m_0 = \sum_{\beta \in \pi_2(X,L)} \operatorname{ev}_*[\overline{\mathcal{M}}_1(X,L;J,\beta)] T^{\omega(\beta)} \operatorname{hol}_{\nabla}(\partial\beta) \in CF(L,L)$$

These features of Floer homology are encoded in the superpotential, namely if  $X = \mathbb{CP}^1$  is a Kähler manifold,  $D = \{0, \infty\}$  the anticanonical divisor (so  $s_D \in H^0(K_X^{-1})$ ),  $\Omega = s_D^{-1} \in H^0(X \setminus D, K_X)$  where  $\Omega = \frac{dz}{z}$  on  $\mathbb{C}^*$ , then

(3) 
$$M = \{(L, \nabla) | L \text{ special Lagr. torus in } X \setminus D, \nabla \text{ flat } U(1) - \text{ connection} \}$$

is the SYZ mirror to the almost-Calabi-Yau manifold  $X \setminus D$ . For  $L \subset X \setminus D$  special Lagrangian,  $\beta \in \pi_2(X, L)$  has Maslov index  $\mu(\beta) = 2(\beta \cdot D)$ . Note that  $s_D$  gives a trivialization of det (TM) away from D. Now, the expected dimension of  $\overline{\mathcal{M}}(x, L, J, \beta) = n - 3 + \mu(\beta)$ : in our case, the positivity of the intersection implies that  $\mu(\beta) \geq 0$  for holomorphic disks.

Assume that there do not exist nonconstant  $\mu = 0$  holomorphic disks in (X, L), i.e all disks hit D. This is ok for  $\mathbb{CP}^1$ , as the maximum principle implies that there are no disks in  $(\mathbb{C}^*, S^1(r))$ . Assume further that  $\mu = 2$  disks (which hit D once) are regular, which is also ok for  $\mathbb{CP}^1$ . These two assumptions are also ok for toric Fano manifolds, e.g. products of  $\mathbb{CP}^n$ s. Then  $\mu = 2$  moduli spaces are compact (there is no bubbling of disks) of dimension n-1. We can define  $n_{\beta} = \deg (\operatorname{ev}_{0*}[\overline{\mathcal{M}}_1(\beta)])$  to be the number of holomorphic disks in the class  $\beta$  where the boundary contains a generic point in L.

## Definition 1.

(4) 
$$\omega(L, \nabla) = \sum_{\substack{\beta \in \pi_2(X, L) \\ \mu(\beta) = 2}} n_{\beta} z_{\beta}(L, \nabla)$$

where 
$$z_{\beta} = e^{-2\pi \int_{\beta} \omega} \operatorname{hol}_{\partial\beta}(\nabla)$$
.

In our example, the Lagrangian L bounds two  $\mu = 2$  disks D and D' centered at  $0, \infty$  respectively: D contributes z while D' contributes z', and the two are related by

(5) 
$$[D] + [D'] = [\mathbb{CP}^1] \implies zz' = e^{-2\pi \int_{\mathbb{CP}^1} \omega} = e^{-\Lambda}$$

Hence 
$$W = z + z' = z + \frac{e^{-\Lambda}}{z}$$
.

Homological mirror symmetry provides two isomorphisms

(6) 
$$D^{\pi}\operatorname{Fuk}(\mathbb{CP}^{1}) \cong H^{0}MF(W)$$
$$D^{b}\operatorname{Coh}(\mathbb{CP}^{1}) \cong D^{b}\operatorname{Fuk}(\mathbb{C}^{*}, W)$$

with matrix factorizations and "Fukaya-Seidel" category respectively. The first one explains our construction of the mirror. The Fukaya category is actually a collection indexed by "charge"  $\lambda \in \mathbb{C}$ , and Fuk $(\mathbb{CP}^1, \lambda)$  is the set of weakly unobstructed Lagrangians with  $m_0 = \lambda \cdot [L]$ . This is an honest  $A_{\infty}$ -category, as the  $m_0$ 's cancel and the Floer differential squares to zero, whereas from  $\lambda$  to  $\lambda'$  we'd have  $\partial^2 = \lambda' - \lambda$ . For instance, for  $L \cong S^1$ ,  $(L, \nabla)$  is weakly unobstructed, with  $m_0 = W(L, \nabla) \cdot [L]$ . However, HF(L, L) = 0 unless L is the equator and  $hol(\nabla) = \pm id$ . For  $p \in L$ ,

(7) 
$$\partial([p]) = z \cdot \text{ev}_{0*}([\mathcal{M}_2(L, [D])] \cap \text{ev}_1^{-1}(p)) + z' \cdot \text{ev}_{0*}([\mathcal{M}_2(L, [D'])] \cap \text{ev}_1^{-1}(p)) = z \cdot [L] - z' \cdot [L]$$

Hence the unit [L] is in the image of  $\partial$  unless  $z = \frac{e^{-\Lambda}}{z}$ , i.e.  $z = \pm e^{-\Lambda/2}$ , i.e. L is the equator. In this case, the contributions of pairs of symmetric disks cancel exactly, and  $HF^*(L,L) \cong H^*(S^1;\mathbb{C})$  as a  $\mathbb{Z}/2\mathbb{Z}$ -graded vector space. However, the product structure is deformed, as  $m_2([p],[p]) = \pm e^{\Lambda/2}[1]$ , i.e. multiplicatively  $HF^*(L,L) \cong \mathbb{C}[t]/t^2 = \pm e^{-\Lambda/2}$ .

---

MIT OpenCourseWare http://ocw.mit.edu

18.969 Topics in Geometry: Mirror Symmetry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## MIRROR SYMMETRY: LECTURE 25

## DENIS AUROUX

Last time, we were considering  $\mathbb{CP}^1$  mirror to  $\mathbb{C}^*, W = z + \frac{e^{-\Lambda}}{z}$  for  $\Lambda = 2\pi \int_{\mathbb{CP}^1} \omega$ : the latter object is a Landau-Ginzburg model, i.e. a Kähler manifold with a holomorphic function called the "superpotential". Homological mirror symmetry gave

(1) 
$$D^{\pi} \operatorname{Fuk}(\mathbb{CP}^{1}) \cong H^{0} M F(W)$$
$$D^{b} \operatorname{Coh}(\mathbb{CP}^{1}) \cong D^{b} \operatorname{Fuk}(\mathbb{C}^{*}, W)$$

We stated that the Fukaya category of  $\mathbb{CP}^1$  was a collection indexed by "charge"  $\lambda \in \mathbb{C}$ , and defined Fuk( $\mathbb{CP}^1, \lambda$ ) to be the set of weakly unobstructed Lagrangians with  $m_0 = \lambda \cdot [L]$ . This is an honest  $A_{\infty}$ -category, as the  $m_0$ 's cancel and the Floer differential squares to zero, whereas from  $\lambda$  to  $\lambda'$  we'd have  $\partial^2 = \lambda' - \lambda$ . For instance, for  $L \cong S^1$ ,  $(L, \nabla)$  is weakly unobstructed, with  $m_0 = W(L, \nabla) \cdot [L]$ . However, HF(L, L) = 0 unless L is the equator and  $hol(\nabla) = \pm id$ . Then  $L_{\pm}$  has  $HF \cong H^*(S^1, \mathbb{C})$  with deformed multiplicative structure,  $HF^*(L, L) \cong \mathbb{C}[t]/t^2 = \pm e^{-\Lambda/2}$ .

We now look at the matrix factorizations of  $W - \lambda, \lambda \in \mathbb{C}$ . These are  $\mathbb{Z}/2\mathbb{Z}$ -graded projective modules Q over the ring of Laurent polynomials  $R = \mathbb{C}[\mathbb{C}^*] \cong \mathbb{C}[z^{\pm 1}]$  equipped with  $\delta \in \operatorname{End}^1(Q)$  s.t.  $\delta^2 = (W - \lambda) \cdot \operatorname{id}_Q$ . That is, we have maps  $\delta_0 : Q_0 \to Q_1, \delta_1 : Q_1 \to Q_0$  given by matrices with entries in the space of Laurent polynomials s.t.  $\delta_0 \circ \delta_1 = (W - \lambda) \cdot \operatorname{id}_{Q_1}, \delta_1 \circ \delta_0 = (W - \lambda) \cdot \operatorname{id}_{Q_0}$ . Now  $\operatorname{Hom}(Q, Q')$  is  $\mathbb{Z}/2\mathbb{Z}$  graded, with

(2) 
$$\operatorname{Hom}^{0} = \left\{ \begin{array}{c} Q_{0} \xrightarrow{\delta_{0}} Q_{1} \\ \downarrow f_{0} \downarrow & \downarrow f_{1} \\ Q'_{0} \xrightarrow{\delta_{0}} Q'_{1} \end{array} \right\}$$

This has a differential  $\partial$  s.t.  $\partial(f) = \delta' \cdot f \pm f \cdot \delta$  and  $\partial^2 = 0$ . We obtain a homology category  $H^0MF(W - \lambda)$ : hom  $= H^0(\text{Hom}, \partial)$ , i.e. "chain maps" up to "homotopy".

**Theorem 1.**  $H^0(MF(W-\lambda)) = 0$ , i.e. all matrix factorizations are nullhomotopic, unless  $\lambda$  is a critical value of W.

Warning: again, looking at homomorphisms from  $MF(W-\lambda)$  to  $MF(W-\lambda')$ , then  $\partial^2 \neq 0$ ,  $\partial^2(f) = {\partial'}^2 \cdot f - f \cdot \partial^2 = (\lambda - \lambda')f$ .

Example.  $W=z+\frac{e^{-\lambda}}{z}$  has critical points  $\pm e^{-\Lambda/2}$  with critical values  $\pm 2e^{-\Lambda/2}$ . Then

(3) 
$$W \pm 2e^{-\Lambda/2} = z \pm 2e^{-\Lambda/2} + \frac{e^{-\lambda}}{z} = (z \pm e^{-\Lambda/2})(1 \pm \frac{e^{-\Lambda/2}}{z})$$
$$Q_{\pm} = \{ \mathbb{C}[z^{\pm 1}] \xrightarrow{z \pm e^{-\Lambda/2} z^{-1}} \mathbb{C}[z^{\pm 1}] \}$$

Then

(4) 
$$\operatorname{End}_{H^{0}MF}(Q_{\pm}) = \{ R \xrightarrow{} R \} / \operatorname{homotopy} \\ \downarrow^{f} \downarrow^{f} \\ R \xrightarrow{} R$$

is multiplication by  $f \in \mathbb{C}[z^{\pm 1}]$ . The maps  $\partial$  sends

(5) 
$$R \xrightarrow{R} R \mapsto R \xrightarrow{R} R$$

$$(x \pm e^{-\Lambda/2})h \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow$$

and similarly on the other side, so

(6) 
$$\operatorname{End}(Q_{\pm}) = \mathbb{C}[z^{\pm 1}]/(z \pm e^{-\Lambda/2}, 1 + \pm e^{-\Lambda/2}z^{-1}) \cong (\mathbb{C}[z^{\pm 1}]/z \pm e^{-\Lambda/2}) \cong \mathbb{C}$$
  
Similarly  $\operatorname{Hom}_{H^0MF}(Q_{\pm}, Q_{\pm}[1]) \cong \mathbb{C}$ .

Indeed, in the case of the two maps z - c,  $1 - cz^{-1}$ , we take vertical maps z, 1, so

(7) 
$$R \xrightarrow{z-c} R$$

$$z \downarrow 1-cz^{-1} \downarrow 1$$

$$R \xrightarrow{z-c} R$$

giving us  $\mathbb{C}[z^{\pm 1}]/\langle z-c\rangle$ .

Next,  $D^b\operatorname{Coh}(\mathbb{CP}^1)$  is generated by  $\mathcal{O}(-1)$  and  $\mathcal{O}$ , i.e. the smallest full subcategory containing  $\mathcal{O}, \mathcal{O}(-1)$  and closed under shifts and cones contains all of  $D^b$ . More generally, via Beilinson we have that

(8) 
$$D^{b}\operatorname{Coh}(\mathbb{CP}^{n}) = \langle \mathcal{O}(-n), \dots, \mathcal{O}(-1), \mathcal{O} \rangle$$

The idea is the the diagonal  $\Delta \subset \mathbb{CP}^n \times \mathbb{CP}^n$  is the (transverse) zero set of  $s = \sum_{i=0}^n \frac{\partial}{\partial x_i} \otimes y_i$ , which is a section of  $E = T(-1) \boxtimes \mathcal{O}(1) = \pi_1^*(T\mathbb{CP}^n \otimes \mathbb{CP}^n)$ 

 $\mathcal{O}(-1)$ )  $\otimes \pi_2^* \mathcal{O}(1)$ . Recall that  $T\mathbb{CP}^n$  is spanned by the vector fields  $x_i \frac{\partial}{\partial x_i}$  on  $\mathbb{C}^{n+1}$  under the relation  $\sum_{i=0}^n x_i \frac{\partial}{\partial x_i} = 0$ . Taking the Koszul resolution

(9) 
$$0 \to E^* = \Omega^1(1) \boxtimes \mathcal{O}(-1) \to \mathcal{O} \boxtimes \mathcal{O} \to \mathcal{O}_{\Delta} \to 0$$

in  $D^b\mathrm{Coh}(\mathbb{P}^1\times\mathbb{P}^1)$ . On the other hand,  $\mathcal{E}\in D^b\mathrm{Coh}(X\times Y)$  gives  $\phi^{\mathcal{E}}:D^b(\mathrm{Coh}(X)\to D^b\mathrm{Coh}(Y), \mathcal{F}\mapsto R\pi_{2*}(L\pi_1^*\mathcal{F}\overset{L}{\otimes}\mathcal{E})$ . Exactness implies that  $\phi^{\mathcal{O}_{\Delta}}(\mathcal{F})\cong \mathcal{F}$  sits in an exact triangle with

(10) 
$$\phi^{\Omega^1 \boxtimes \mathcal{O}(-1)}(\mathcal{F}) \cong R\Gamma(\mathcal{F} \otimes \Omega^1(1)) \otimes_{\mathbb{C}} \mathcal{O}(-1)$$
$$\phi^{\mathcal{O} \boxtimes \mathcal{O}}(\mathcal{F}) \cong R\Gamma(\mathcal{F}) \otimes_{\mathbb{C}} \mathcal{O}$$

which completes the proof.

The algebra of the exceptional collection  $\langle \mathcal{O}(-1), \mathcal{O} \rangle$  is given by

(11) 
$$\mathcal{A} = \operatorname{End}^*(\mathcal{O}(-1) \oplus \mathcal{O})$$

and  $D^B$ Coh( $\mathbb{CP}^1$ ) is isomorphic to the derived category of finitely-generated  $\mathcal{A}$ -modules.

Finally, the Fukaya category of  $(\mathbb{C}^*, W = z + \frac{e^{-\Lambda}}{2})$  is the category whose objects are admissible Lagrangians with flat connections, i.e. L is a (possibly noncompact) Lagrangian submanifold with  $W|_L$  proper,  $W|_L \in \mathbb{R}_+$  outside a compact subset. We can perturb such L: for  $a \in \mathbb{R}$ , let  $L^{(a)}$  be Hamiltonian isotopic to L,  $W(L^{(a)}) \in \mathbb{R}_+ + ia$  near  $\infty$ . In good cases, it will be the Hamiltonian flow of  $X_{\text{Re }(W)} = \nabla \text{Im } W$ . Then  $\text{Hom}(L, L') = CF^*(L^{(a)}, L'^{(a')})$  for a > a' (the Floer differential is well-defined), and we obtain  $m_k, k \geq 2$  similarly, perturbing the Lagrangians so they are in decreasing order of Im (W).

Example. Consider  $L_0 = \mathbb{R}_+$ ,  $L_{-1} =$  an arc joining 0 to  $+\infty$  and rotating once clockwise around the origin. Then  $e^{-\Lambda/2} \in L_0$ ,  $-e^{-\Lambda/2} \in L_{-1}$ , so under  $W = z + \frac{e^{-\Lambda}}{z}$ , we have  $W(L_0)$  being the interval  $[2e^{-\Lambda/2}, +\infty)$  on the positive real axis, while  $W(L_{-1})$  is an arc that joins  $-2e^{-\Lambda/2}$  to  $+\infty$  in the lower half plane. Furthermore,  $\text{hom}(L_0, L_0) \cong \mathbb{C} \cdot e, e = \text{id}_{L_0}$ , and same for  $L_{-1}$ , while  $\text{hom}(L_0, L_{-1}) = 0$  and  $\text{hom}(L_{-1}, L_0) = V$  has dimension 2. Then  $\text{Fuk}(\mathbb{C}^*, W)$  is generated by  $L_{-1}, L_0$  (Seidel)

Similarly, one can obtain homological mirror symmetry for toric Fano manifolds: see M. Abouzaid.
