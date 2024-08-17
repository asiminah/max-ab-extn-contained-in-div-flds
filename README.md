# max-ab-extn-contained-in-div-flds

This repository contains code and data associated to the paper "Maximal abelian extensions contained in division fields of elliptic curves over $\mathbb{Q}$ with complex multiplication", by Asimina S. Hamakiotes, arXiv:"number" (2024).


The ```ComputeMaxAbExtn.m``` file contains the following: 
* testing
* ok

The ```VerifyComputations.m``` file contains code that verifies the computations done in Section 5 of the paper, as well as the code used for the proof of Lemma 5.2. The file has the following: 
* **Theorem 1.1:** ```VerifyThm11SplitIndex1Cases()``` and ```VerifyThm11SplitIndex3Case()``` verify the computations done for images that are contained in the normalizer of the split Cartan and have index 1 and 3, respectively; ```VerifyThm11NonSplitIndex1Cases()``` and ```VerifyThm11NonSplitIndex3Case()``` verify the computations done for images that are contained in the normalizer of the non-split Cartan and have index 1 and 3, respectively.
* **Theorem 1.2:** ```VerifyThm12Index1()``` and ```VerifyThm12Index2()``` verify the computations done for images that have index 1 and index 2 in the normalizer of Cartan, respectively.
* **Theorem 1.3:** ```VerifyThm13Index1()``` and ```VerifyThm13Index2()``` verify the computations done for images that have index 1 and 2 in the normalizer of Cartan, respectively; ```VerifyThm13Index3and6()``` verifies the computations done for images that have index 3 and 6 in the normalizer of Cartan.  
* ```VerifyAllComputations()``` verifies all the computations in Section 5 of the paper. 

