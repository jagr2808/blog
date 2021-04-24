---
title: "Kan extensions"
date: 2020-05-30T21:09:44+02:00
display_image: '/kan/cone.png'
tags: ['(co)limit', 'Category theory', 'Kan extensions']
draft: false
---

`\(
\DeclareMathOperator{\Spec}{Spec}
\DeclareMathOperator{\C}{\mathbb{C}}
\DeclareMathOperator{\Z}{\mathbb{Z}}
\DeclareMathOperator{\Hom}{Hom}
\DeclareMathOperator{\Mod}{Mod}
\)`

Recently I learned about Kan extension which is a generalization of (co)limits in category theory. So I thought it would be fun to write a little blog post introducing limits and Kan extensions. The idea of a (co)limit is to capture information about a diagram in just one object. The idea of Kan extensions is similar, but instead of trying to capture information in a single object we do it in some other diagram. The word "extension" in Kan extension comes from what happens if the diagram we use to capture the information is bigger than the original diagram; we are extending the diagram. I will try to make this very loose explanation more rigorous in this post, so let's begin.

**Definition (diagram)**: If `$A$` is a small category and `$\mathcal{C}$` is a (not necessarily small) category, then a diagram in `$\mathcal{C}$` in the shape of `$A$` is a functor `$X: A \to \mathcal{C}$.

For example if `$A = 2$` is the discrete category with two objects then a diagram of shape `$A$` is just a pair of objects in `$\mathcal{C}$`. Or if `$A = A_L \leftarrow A_0 \rightarrow A_R$` an `$A$`-shaped diagram is three objects in `$\mathcal{C}$` together with two morphisms between the appropriate objects.

Both the (co)limit and a Kan extension are universal constructions. A universal construction is done by looking at all the "candidates" that encapsulates the information we wish to capture. Then the universal construction is the candidate that can capture the information of all the other candidates. Let's have a quick refresher of what this candidate is in the (co)limit case.

**Definition ((co)cone)**: For an object `$C \in \mathcal{C}$` we have a functor `$\Delta(C): A \to \mathcal{C}$` that maps every object of `$A$` to `$C$` and every morphism of `$A$` to `$1_C$` the identity morphism on `$C$`. A cone of a diagram `$X:A \to \mathcal{C}$` is a natural transformation `$\eta : \Delta(C) \Rightarrow X$`. Similarly a cocone is a natural transformation `$\varepsilon: X \Rightarrow \Delta(C)$`.

The (co)cone is so named because of how it looks when you draw it 

![A cone of X](/kan/cone.png)

So the limit is the cone that capture the information of all other cones. More specifically for every cone `$\eta: \Delta(C) \to X$` there is a unique morphism `$C \to \lim X$`, and vice versa. So the cones of `$X$` are in correspondence with the morphisms to `$\lim X$`. It is in this way that the limit encapsulates all other cones. Similarly the cocones are in correspondence with all the morphisms from the colimit`.

Like I said before a Kan extension is really the same idea, but instead of looking at a single object we look at another diagram. How would we do this you might ask? The thing to realize is that a single object IS another diagram, just in a very specific shape. It is in the shape of 1, the discrete category with one object. A functor from 1 just picks out a single object and a natural transformation between to such diagrams is just a morphism between their objects. Further the functor `$\Delta: \mathcal{C} \to \mathcal{C}^A$` is really just precomposition with the unique functor `$\pi_A: A \to 1$`. So a cone is really a functor `$C:1 \to \mathcal{C}$` together with a natural transformation `$\eta: \pi_A^* C \Rightarrow X$`.

![A cone as a natural transformation](/kan/cone-as-kan.png)

with this picture in mind we can define Kan extensions.

**Definition (Kan extension)**: Let `$A$` and `$B$` be small categories, `$\mathcal{C}$` a category, `$u: A \to B$` a functor, and `$X:A \to \mathcal{C}$` a diagram. The Right Kan extension of `$X$` along `$u$` is a functor `$RKan_u(X) : B \to \mathcal{C}$` together with a natural transformation `$\alpha: RKan_u(X) \circ u \Rightarrow X$`, such that for any other functor `$Y: B \to \mathcal{C}$` and natural transformation `$\eta: Y \circ u \Rightarrow X$` there is a unique natural transformation `$\hat{\eta} : Y \Rightarrow RKan_u(X)$` such that `$\alpha \cdot \hat{\eta} \circ u = \eta$`.

![Kan extension](/kan/kan-extension.png)

Another way to say this is that we have a natural isomorphism `$\Hom_{\mathcal{C}^B}(Y, RKan_u(X)) \cong \Hom_{\mathcal{C}^A}(u^*Y, X)$`, i.e. `$(u^*, RKan)$` is an adjoint pair. Dually the Left Kan extension is defined as the left adjoint of the precomposition functor `$u^*$`.

Lastly let's look at an example. We can think of a group as a category with one object. That is if `$G$` is a group we make a category with one object `$*$`, and morphisms `$\Hom(*,*) = G$` such that composition is the group operation of `$G$`. Then a functor `$\varphi: H \to G$` corresponds exactly to a group map between the groups, a functor `$\rho: G \to \mathcal{C}$` is exactly a `$G$` action on an object of `$\mathcal{C}$`, and a natural transformation between such functors corresponds exactly to a `$G$`-linear map between `$G$`-objects. 

Example: Let `$G$` be a group (realized as a category), `$H$` a subgroup of `$G$`, `$\iota : H \to G$` the inclusion functor and `$X: H \to Ab$` an `$H$`-module. Then the Left Kan extension of `$X$` along `$\iota$` is the induced module `$\mathbb{Z}G \otimes_{\mathbb{Z}H} X$`, and the Right Kan extension is the coinduced module `$\Hom_{\mathbb{Z}H}(\mathbb{Z}G, X)$`. The natural transformations are given by `$x \mapsto 1 \otimes x$` and `$f \mapsto f(1)$` respectively.

proof. I will prove that the coinduced module is the Right Kan extension, the proof for the induced module is similar. The first thing we should check is that `$\alpha = \left(f \mapsto f(1)\right)$` actually is a natural transformation, i.e. we must check that it is `$H$`-linear. The action on `$\Hom_{\mathbb{Z}H}(\mathbb{Z}G, X)$` is given by `$(gf)(s) = f(sg)$`, so `$\alpha(hf) f(1\cdot h) = f(h)$`. Since `$f$` is `$H$`-linear we have that `$f(h) = hf(1) = h\alpha(f)$` and so `$\alpha$` is natural.

Now assume `$Y$` is some other `$G$`-module and `$\eta: \iota^*Y \to X$` is an `$H$`-linear map. Then we need to show that there is a unique `$G$`-linear map `$\hat{\eta}: Y \to \Hom_{\mathbb{Z}H}(\mathbb{Z}G, X)$` such that `$\alpha \cdot \hat{\eta} \circ \iota = \eta$`. For ease of notation let us write `$f_y$` for `$\hat{\eta}(y)$`. Then if we want `$\eta$` to factor through `$\hat{\eta}$` we need `$f_y(1) = \eta(y)$`. If `$\hat{\eta}$` is to be `$G$`-linear we need `$f_{gy}=gf_y$`, but then `$f_y(g) = (gf_y)(1) = f_{gy}(1) = \eta(gy)$`. This shows that `$\hat{\eta}$` is unique. The only thing that needs to be checked then for `$\hat{\eta}$` to be well defined is that `$f_y$` is `$H$`-linear. I leave this to you.
