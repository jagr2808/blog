---
title: "AR Duality"
date: 2020-09-14T12:00:04+02:00
display_image: '/AR-duality/factor-through-projective.png'
tags: ["Representation Theory", "AR Theory"]
draft: false
---

`\(
\require{AMScd}
\DeclareMathOperator{\Hom}{Hom}
\DeclareMathOperator{\Ext}{Ext}
\DeclareMathOperator{\End}{End}
\DeclareMathOperator{\proj}{proj}
\def\L{\Lambda}
\def\mod{\operatorname{mod}}
\)`

In this blogpost I want to talk about the concept of AR duality. In short AR duality says that in suitably nice abelian categories we have natural isomorphisms 
`$$\underline{\Hom}(\tau^- Y, X) \cong D\Ext^1(X, Y) \cong \overline{\Hom}(Y, \tau X)$$`
Where `$\underline{\Hom}$` is the stable homfunctor, `$\overline{\Hom}$` is the costable homfunctor and `$\tau$` is the Auslander-Reiten translate. In this blogpost I will define what these things mean and try to give an outline of the proof.

# Preliminaries and notation
Throughout this blogpost `$k$` will be a field and `$\Lambda$` a finite dimensional algebra over `$k$`. We write `$\mod \Lambda$` to refer to the category of finitely generated `$\Lambda$`-modules, and `$\mod \Lambda^{op}$` the category of finitely generated right `$\Lambda$`-modules (or equivalently left `$\Lambda^{op}$`-modules). We will denote by `$S_i$` for `$i=1, \cdots, n$` the simple `$\Lambda$`-modules, and `$P_i$` and `$I_i$` for the projective cover and injective envelope of `$S_i$`. Similarly `$S_i'$`, `$P_i'$` and `$I_i'$` refer to the simple `$\Lambda^{op}$`-modules and their projective covers and injective envelopes.

We think of the elements of `$\Ext^1_\L(X, Y)$` as Yoneda extensions, i.e. an element `$\eta \in \Ext^1_\L(X, Y)$` corresponds to a sequence

`$$\begin{CD}
\eta: \; @. 0 @>>> Y @>>> E_\eta @>>> X @>>> 0
\end{CD}$$`

up to isomorphism. If `$f: Y \to Y'$` and `$g: X' \to X$` are morphisms then `$f\eta$` adn `$\eta g$` are the unique extensions fitting into the commutative diagram

`$$\begin{CD}
\eta g: \; @. 0 @>>> Y @>>> E_{\eta g} @>>> X' @>>> 0\\
@. @VVV @| @VVV @VVgV @VVV\\
\eta: \; @. 0 @>>> Y @>>> E_\eta @>>> X @>>> 0\\
@. @VVV @VVfV @VVV @| @VVV\\
f\eta: \; @. 0 @>>> Y @>>> E_{f\eta} @>>> X @>>> 0.\\
\end{CD}$$`

This construction is bifunctorial so `$(f\eta)g = f(\eta g)$`, and it respects composition. Another thing to note is that `$E_{\eta g}$` is pullback and `$E_{f\eta}$` is pushout.

# AR translate
When working with `$\L$`-modules we have two important dualities. `$(-)^* = \Hom_\Lambda(-, \Lambda):\proj \Lambda \to \proj \Lambda^{op}$` which maps projective left `$\Lambda$`-modules to projective right `$\Lambda$`-modules. And `$D = \Hom_k(-,k): \mod \Lambda \to \mod \Lambda^{op}$` mapping left modules to right modules. The important thing to note about these dualities is that if we define `$S_i'$` as `$DS_i$` then `$P_i^* =  P_i'$` and `$DP_i = I_i'$`. We can use these dualities to define the Auslander Reiten translate. 

**Definition (AR translate)**: Let `$M$` be a `$\L$`-module and `$P_1^M \to P_0^M \to M$` the minimal projective presentation of `$M$`. Applying our first duality we get a map `${P_0^M}^* \to {P_1^M}^*$`. Applying the second duality we get a map `$D{P_1^M}^* \to D{P_0^M}^*$`. The AR translate `$\tau M$` is defined to be the kernel of this map.

What we're essentially doing is replacing the projective modules in the presentation of `$M$` by the corresponding injective modules, and then taking the kernel instead of the cokernel. For example if we let `$\L$` be the path algebra `$k\left[ 1 \to 2 \to 3 \right]$`, then the minimal projective presentation of `$S_1$` is `$P_2 \to P_1$`. Applying the two dualities we get `$I_2 \to I_1$` which has kernel `$S_2$`. Hence the AR translate of `$S_1$` is `$\tau S_1=S_2$`.

for any projective module `$P$`, it's minimal presentation is simply `$0 \to P$`, thus `$\tau P = 0$`. But if we ''ignore'' the projectives then `$\tau$` is an equivalence! More explicitly `$\tau: \underline{\mod}\L \to \overline{\mod}\L$` is an equivalence between the stable and costable module category. The stable module category is the one we get if we replace every projective module with the 0-module. For this to make sense we also have to replace any morphism factoring through a projective with the 0-morphism, since any map that factors through 0 is 0. The costable category is exactly the same, but for injective objects instead.

# Almost split sequences
An important reason to care about the AR translate is almost split sequences. A morphism is right almost split if it's *almost* split epi. To be more precise a morphism is right almost split if it is not split epi, and any map that isn't split epi factors through it. This definition makes sense since for a split epimorphism, any map factors through it. So a right almost split map is as close to being split epi as it could be without actually being. Dually we define a left almost split map as a map that is almost split mono.

For any indecomposable `$\L$`-module `$M$` there is a unique right almost split map ending in `$M$`, and the kernel of this map is `$\tau M$` (In a more general abelian category this might be how you define `$\tau$`). Further if `$M$` is not projective this map is epi, and the kernel map is left almost split. So we have short exact sequence

`$$\begin{CD}
 0 @>>> \tau M @>>> E @>>> M @>>> 0
\end{CD}$$`

which we call the almost split sequence of `$M$`, and will denote by `$\alpha_M$`. Further for any non-split sequence `$\eta \in \Ext^1_\L(X, \tau M)$` there is a map `$f:M \to X$` such that `$\eta f$` is the almost split sequence. To see this let `$\eta$` be the sequence

`$$\begin{CD}
0 @>>> \tau M @>>> F @>>> X @>>> 0.
\end{CD}$$`

Since `$\tau M \to F$` isn't split and `$\tau M \to E$` is almost split, there is a map `$E \to F$` making the following diagram commute

`$$\begin{CD}
0 @>>> \tau M @>>> E @>>> M @>>> 0\\
@VVV @| @VVV @. @VVV \\
0 @>>> \tau M @>>> F @>>> X @>>> 0.
\end{CD}$$`

If we let `$f:M \to X$` be the induced map of cokernels we get that `$\eta f$` is our split exact sequence. A similar argument can also be made for non-split sequences in `$\Ext^1_\L(M, X)$`.

# The main theorem
We want to prove that `$D\Ext_\L^1(X, Y)$` is naturally isomorphic to `$\underline{\Hom}(\tau^- Y, X)$` in `$X$` and `$Y$`. Since these are both additive functors, it is enough to restrict to the case when `$X$` and `$Y$` are indecomposable. We do this by constructing a perfect pairing between `$\Ext_\L^1(X, Y)$` and `$\underline{\Hom}(\tau^- Y, X)$`. A perfect pairing is a bilinear map `$\langle -,- \rangle: \Ext_\L^1(X, Y) \times \underline{\Hom}(\tau^- Y, X) \to k$` such that for any non-zero element `$\eta \in \Ext_\L^1(X, Y)$` there is an `$f \in  \underline{\Hom}(\tau^- Y, X)$` such that `$\langle \eta, f \rangle \neq 0$`, and conversely for every non-zero `$f$` there is an `$\eta$`. A perfect pairing would induce an isomorphism `$\underline{\Hom}(\tau^- Y, X) \cong D\Ext_\L^1(X, Y)$` by mapping `$f$` to `$\langle - , f \rangle$`, which is what we want.

Since `$\alpha_{\tau^-Y} \in \Ext_\L^1(\tau^- Y, Y)$` is non-zero there is a functional `$\mu \in D\Ext_\L^1(\tau^- Y, Y) = \Hom_k(\Ext_\L^1(\tau^- Y, Y), k)$` such that `$\mu(\alpha_{\tau^-Y}) \neq 0$`. We can then define our pairing as `$\langle \eta, f \rangle = \mu(\eta f)$`. First we want to check that this pairing is well defined. Let `$f$` be a map that factors through a projective, and thus is 0 in `$\underline{\Hom}(\tau^- Y, X)$`.

![Morphism factoring through projective](/AR-duality/factor-through-projective.png)

Since `$P$` is projective we can lift the map `$E_\eta \to X$` to `$P$`, and then by composing we get that `$f$` factors through `$E_\eta \to X$`. This means we have a commutative square:

`$$\begin{CD}
\tau^-Y @= \tau^-Y\\
@VVV @VVV\\
E_\eta @>>> X
\end{CD}$$`

Then by the pullback property we get that the identity on `$\tau^- Y$` factors trough `$E_\eta \prod\limits_X \tau^- Y \to \tau^- Y$`. So `$\eta f$` is split and thus 0 in `$\Ext_\L^1(\tau^- Y, Y)$`.

Next we want to check that for any nonzero `$\eta \in \Ext_\L^1(X, Y)$` there is an `$f \in \underline{\Hom}(\tau^- Y, X)$` such that `$\langle \eta, f\rangle \neq 0$`. Let `$\eta$` be 

`$$\begin{CD}
0 @>>> Y @>>> E_\eta @>>> X @>>> 0
\end{CD}$$`

and let 

`$$\begin{CD}
0 @>>> Y @>>> E @>>> \tau^-Y @>>> 0
\end{CD}$$`

be the almost split sequence `$\alpha_{\tau^-Y}$`. Then since `$Y \to E_\eta$` isn't split it factors through the almost split map `$Y \to E$`. Taking cokernels we get the diagram

`$$\begin{CD}
0 @>>> Y @>>> E @>>> \tau^-Y @>>> 0\\
@VVV @VVV @VVV @VVV @VVV\\
0 @>>> Y @>>> E_\eta @>>> X @>>> 0
\end{CD}$$`

Thus there is a map `$f:\tau^-Y \to X$` such that `$\eta f = \alpha_{\tau^-Y}$`, and we have that `$\langle \eta, f \rangle = \mu(\eta f) = \mu(\alpha_{\tau^-Y}) \neq 0$`.

For the other direction assume `$f:\tau^-Y \to X$` is a map that does not factor through any projective. Let `$P \to X$` be an epimorphism from a projective to `$X$`, and let `$K$` be its kernel. If we take the pullback with `$f$` we get an extension of `$\tau^-Y$` and `$K$`

`$$\begin{CD}
0 @>>> K @>>> P @>>> X @>>> 0\\
@AAA @| @AAA @AAfA @AAA\\
0 @>>> K @>>> E_X @>>> \tau^-Y @>>> 0
\end{CD}$$`

This extension cannot be split because if it was `$f$` would factor though `$P$`, and since we assumed `$f$` doesn't factor through a projective this is impossible. So the extensions isn't split in particular the map `$E_X \to \tau^-Y$` is not split epi. This means that it factors through the almost split sequence. Thus there is a map `$g:K\to Y$` giving us the folowing diagram

`$$\begin{CD}
0 @>>> K @>>> P @>>> X @>>> 0\\
@AAA @| @AAA @AAfA @AAA\\
0 @>>> K @>>> E_X @>>> \tau^-Y @>>> 0\\
@VVV @VVgV @VVV @| @VVV\\
0 @>>> Y @>>> E @>>> \tau^-Y @>>> 0\\
\end{CD}$$`

Interchanging the order of when we do pushout and pullback we get a diagram like

`$$\begin{CD}
0 @>>> K @>>> P @>>> X @>>> 0\\
@VVV @VVgV @VVV @| @VVV\\
0 @>>> Y @>>> Y \coprod\limits_K P @>>> X @>>> 0\\
@AAA @| @AAA @AAfA @AAA\\
0 @>>> Y @>>> E @>>> \tau^-Y @>>> 0\\
\end{CD}$$`

Calling the middle sequence `$\eta$` we get that `$\eta f = \alpha_{\tau^-Y}$` and thus `$\langle \eta, f \rangle \neq 0$`.

This shows that we have a perfect pairing `$\langle -,- \rangle: \Ext_\L^1(X, Y) \times \underline{\Hom}(\tau^- Y, X) \to k$` which gives us an isomorphism `$\underline{\Hom}(\tau^- Y, X) \cong D\Ext_\L^1(X, Y)$`. It's pretty straight forward to see that this isomorphism is functorial in `$X$`. To get something functorial in `$Y$` aswell we just have to choose our functionals `$\mu \in D\Ext_\L^1(\tau^- Y, Y)$` in a compatible way. This can be done, but I will not dwell on the details here.

The AR duality gives a nice way to compute `$\Ext^1$`. Especially in the case when `$\L$` is hereditary, becuase then `$\underline{\Hom}(Y, X) = \Hom(Y, X)$` whenever `$Y$` has no projective summands. This is the basis for something called `$\tau$`-tilting theory, which is a generalization of tilting theory where we replace the condition `$\Ext^1(T, T) = 0$` with `$\Hom(T, \tau T) = 0$`. That's all I had to say for now.
