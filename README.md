# max-ab-extn-contained-in-div-flds

This repository contains code and data associated to the paper "Maximal abelian extensions contained in division fields of elliptic curves over $\mathbb{Q}$ with complex multiplication", by Asimina S. Hamakiotes, arXiv:"number" (2024).


The ```ComputeMaxAbExtn.m``` file contains the following: 
* testing
* ok

The ```VerifyComputations.m``` file contains code that verifies the computations done in Section 5 of the paper, as well as the code used for the proof of Lemma 5.2. The file has the following: 
* ```VerifyThm11SplitIndex1Cases()``` verifies the computations done in Theorem 1.1 for an image that is contained in the normalizer of the split Cartan and has index 1.
* ```VerifyThm11SplitIndex3Case()``` verifies the computations done in Theorem 1.1 for an image that is contained in the normalizer of the split Cartan and has index 3.
* ```VerifyThm11NonSplitIndex1Cases()``` verifies the computations done in Theorem 1.1 for an image that is contained in the normalizer of the non-split Cartan and has index 1.
* ```VerifyThm11NonSplitIndex3Case()``` verifies the computations done in Theorem 1.1 for an image that is contained in the normalizer of the non-split Cartan and has index 3.
* ```VerifyThm12Index1()``` verifies the computations done in Theorem 1.2 for an image that has index 1 in the normalizer of Cartan.
* ```VerifyThm12Index2()``` verifies the computations done in Theorem 1.2 for an image that has index 2 in the normalizer of Cartan. 
* ```VerifyAllComputations()``` verifies all the computations in Section 5 of the paper. 
* ok
