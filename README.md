# max-ab-extn-contained-in-div-flds

This repository contains code and data associated to the paper "Maximal abelian extensions contained in division fields of elliptic curves over $\mathbb{Q}$ with complex multiplication", by Asimina S. Hamakiotes, arXiv:2408.16164 (2024).


The ```ComputeMaxAbExtn.m``` file contains code that does the following: 
* Given an elliptic curve $E/\mathbb{Q}$ with CM, ```ComputeTwist(E)``` returns the twisting factor $\alpha$ of $E$ such that $E^\alpha$ is one of the curves in Table 1 of the paper, and returns the curve that it is a twist of. 
* Given an elliptic curve $E/\mathbb{Q}$ with CM and a prime $p$, ```MaxAbExtn(E,p)``` returns the maximal abelian extension contained in $\mathbb{Q}(E[p^n])/\mathbb{Q}$ for $n \geq 2$.
* ```VerifyAllExamples()``` verifies all of the examples in Section 2 of the paper. 

The ```VerifyComputations.m``` file contains code that verifies the computations done in Section 5 of the paper, as well as the code used for the proof of Lemma 5.2. The file has the following: 
* **Theorem 1.1:** ```VerifyThm11SplitIndex1Cases()``` and ```VerifyThm11SplitIndex3Case()``` verify the computations done for images that are contained in the normalizer of the split Cartan and have index 1 and 3, respectively; ```VerifyThm11NonSplitIndex1Cases()``` and ```VerifyThm11NonSplitIndex3Case()``` verify the computations done for images that are contained in the normalizer of the non-split Cartan and have index 1 and 3, respectively.
* **Theorem 1.2:** ```VerifyThm12Index1()``` and ```VerifyThm12Index2()``` verify the computations done for images that have index 1 and index 2 in the normalizer of Cartan, respectively.
* **Theorem 1.3:** ```VerifyThm13Index1()``` and ```VerifyThm13Index2()``` verify the computations done for images that have index 1 and 2 in the normalizer of Cartan, respectively; ```VerifyThm13Index3and6()``` verifies the computations done for images that have index 3 and 6 in the normalizer of Cartan.
* **Proposition 5.3:** This is part of Theorem 1.4.(a); ```VerifyProp53Split()``` and ```VerifyProp53NonSplit()``` verify the computations done for images that are contained in the normalizer of the split and non-split Cartan, respectively.
* **Proposition 5.4:** This is part of Theorem 1.4.(a); ```VerifyProp54Index1()``` and ```VerifyProp54Index3()``` verify the images that have index 1 and 3 in the normalizer of Cartan, respectively. 
* **Theorem 1.4.(b):** ```VerifyThm14bi()``` verifies the computations done for $\Delta_Kf^2 = -12, -28$; ```VerifyThm14bii()``` verifies the computations done for $\Delta_Kf^2 = -4$; ```VerifyThm14biiiIndex1()``` and ```VerifyThm14biiiIndex2()``` verify the computations done for $\Delta_Kf^2 = -8, -16$. 
* ```VerifyAllComputations()``` verifies all the computations mentioned above that are used in Section 5 of the paper.
* **Lemma 5.2:** ```VerifyLemma52()``` contains the proof of Lemma 5.2. 

