/*
	This code is for the paper "The maximal abelian extension contained in a division field of an elliptic curve over Q with complex multiplication" by Asimina S. Hamakiotes
*/


print " ";
print "Run VerifyAllComputations() in order to verify all the computations in Section 5 of the paper";
print " ";
print "Run VerifyLemma52() to verify Lemma 5.2";
print " ";


//////////////////////////////////////////////////////////////////////////////////////////

//These procedures verify the computations in Theorem 1.1. 


//Function that verifies Theorem 1.1 for the split index 1 cases 
procedure VerifyThm11SplitIndex1Cases()
	print "==================";
	print "Verifying Theorem 1.1 for the split index 1 cases.";
	F<a,b,c,d,p>:=FunctionField(Rationals(),5);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod p^2):";
	A:=G![0,1,1,0]; // mod p^2
	B:=G![a,0,0,b]; // mod p^2
	K:=G![1,0,0,p+1]; // mod p^2. K is an element of ker(pi|_{G_{E,p^2}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^2
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod p^2
	Y := Y1/Y2; // Note that this is not the identity matrix mod p^2, but is mod p
	Y; // Magma will not reduce this mod p^2, so you have to look at it and reduce it yourself.
	y := G![1,0,0,1]; // Let y = Y mod p. Y above reduces to the identity matrix mod p 
	print "Note that this is the identity matrix mod p.";
	print "==================";
	//Induction:
	// Let c = p^n + 1.
	print "Induction (mod p^(n+1)): Let c = p^n + 1.";
	A:=G![0,1,1,0]; // mod p^{n+1}
	B:=G![a,0,0,b]; // mod p^{n+1}
	K:=G![1,0,0,c]; // mod p^{n+1}. K is an element of ker(pi|_{G_{E,p^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod p^{n+1}
	Y := Y1/Y2; // Note that this is not the identity matrix mod p^{n+1}, but is mod p^n
	Y; // Magma will not reduce this mod p^{n+1}, so you may have to reduce it yourself
	y := G![1,0,0,1]; // Let y = Y mod p^n. Y above reduces to the identity matrix mod p^n
	print "Note that this is the identity matrix mod p^n.";
	print "==================";
end procedure;


//Function that verifies Theorem 1.1 for the split index 3 case 
procedure VerifyThm11SplitIndex3Case()
	print "==================";
	print "Verifying Theorem 1.1 for the split index 3 case.";
	F<a,b,c,d,p>:=FunctionField(Rationals(),5);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod p^2):";
	A:=G![0,1,1,0]; // mod p^2
	B:=G![1,0,0,1]; // mod p^2
	K:=G![1,0,0,p+1]; // mod p^2. K is an element of ker(pi|_{G_{E,p^2}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^2
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod p^2
	Y := Y1/Y2; // Note that this is not the identity matrix mod p^2, but is mod p
	Y; // Magma will not reduce this mod p^2, so you have to look at it and reduce it yourself.
	y := G![1,0,0,1]; // Let y = Y mod p. Y above reduces to the identity matrix mod p 
	print "Note that this is the identity matrix mod p.";
	print "==================";
	//Induction:
	// Let c = p^n + 1.
	print "Induction (mod p^(n+1)): Let c = p^n + 1.";
	A:=G![0,1,1,0]; // mod p^{n+1}
	B:=G![1,0,0,1]; // mod p^{n+1}
	K:=G![1,0,0,c]; // mod p^{n+1}. K is an element of ker(pi|_{G_{E,p^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod p^{n+1}
	Y := Y1/Y2; // Note that this is not the identity matrix mod p^{n+1}, but is mod p^n
	Y; // Magma will not reduce this mod p^{n+1}, so you may have to reduce it yourself
	y := G![1,0,0,1]; // Let y = Y mod p^n. Y above reduces to the identity matrix mod p^n
	print "Note that this is the identity matrix mod p^n.";
	print "==================";
end procedure;


//Function that verifies Theorem 1.1 for the non-split index 1 cases 
procedure VerifyThm11NonSplitIndex1Cases()
	print "==================";
	print "Verifying Theorem 1.1 for the non-split index 1 cases.";
	F<a,b,c,d,p>:=FunctionField(Rationals(),5);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod p^2):";
	A:=G![1,0,0,-1]; // mod p^2
	B:=G![a,d*b,b,a]; // mod p^2
	K:=G![1,d*p,p,1]; // mod p^2. K is an element of ker(pi|_{G_{E,p^2}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^2
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod p^2
	Y := Y1/Y2; // Magma will not reduce this mod p^2, so you have to look at it and reduce it yourself.
	Y; 
	Y := G![1, -2*d*p/(d*p^2 - 1), -2*p/(d*p^2 - 1), 1]; // Y := Y1/Y2 reduces to this matrix mod p^2
	print "This matrix reduces mod p^2 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod p. Y above reduces to the identity matrix mod p 
	print "Note that this is the identity matrix mod p.";
	print "==================";
	//Induction:
	// Let c = p^n.
	print "Induction (mod p^(n+1)): Let c = p^n.";
	A:=G![1,0,0,-1]; // mod p^{n+1}
	B:=G![a,d*b,b,a]; // mod p^{n+1}
	K:=G![1,d*c,c,1]; // mod p^{n+1}. K is an element of ker(pi|_{G_{E,p^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod p^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod p^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, -2*c*d/(c^2*d - 1), -2*c/(c^2*d - 1), 1]; // Y := Y1/Y2 reduces to this matrix mod p^{n+1}
	print "This matrix reduces mod p^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod p^n. Y above reduces to the identity matrix mod p^n
	print "Note that this is the identity matrix mod p^n.";
	print "==================";
end procedure;


//Function that verifies Theorem 1.1 for the non-split index 3 case 
procedure VerifyThm11NonSplitIndex3Case()
	print "==================";
	print "Verifying Theorem 1.1 for the non-split index 3 case.";
	F<a,b,c,d,p>:=FunctionField(Rationals(),5);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod p^2):";
	A:=G![1,0,0,-1]; // mod p^2
	B:=G![a,d*b,b,a]; // mod p^2
	B:=B^3;
	K:=G![1,d*p,p,1]; // mod p^2. K is an element of ker(pi|_{G_{E,p^2}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^2
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod p^2
	Y := Y1/Y2; // Magma will not reduce this mod p^2, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, -2*d*p/(d*p^2 - 1), -2*p/(d*p^2 - 1), 1]; // Y := Y1/Y2 reduces to this matrix mod p^2
	print "This matrix reduces mod p^2 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod p. Y above reduces to the identity matrix mod p 
	print "Note that this is the identity matrix mod p.";
	print "==================";
	//Induction:
	// Let c = p^n.
	print "Induction (mod p^(n+1)): Let c = p^n.";
	A:=G![1,0,0,-1]; // mod p^{n+1}
	B:=G![a,d*b,b,a]; // mod p^{n+1}
	B:=B^3;
	K:=G![1,d*c,c,1]; // mod p^{n+1}. K is an element of ker(pi|_{G_{E,p^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod p^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod p^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, -2*c*d/(c^2*d - 1), -2*c/(c^2*d - 1), 1]; // Y := Y1/Y2 reduces to this matrix mod p^{n+1}
	print "This matrix reduces mod p^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod p^n. Y above reduces to the identity matrix mod p^n
	print "Note that this is the identity matrix mod p^n.";
	print "==================";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////

//These procedures verify the computations in Theorem 1.2. 


//Function that verifies Theorem 1.2 for the index 1 case
procedure VerifyThm12Index1()
	print "==================";
	print "Verifying Theorem 1.2 for the index 1 case.";
	F<a,b,c,d,p>:=FunctionField(Rationals(),5);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod p^2):";
	A:=G![-1,0,0,1]; // mod p^2
	B:=G![a,b,d*b,a]; // mod p^2
	K:=G![1,p,d*p,1]; // mod p^2. K is an element of ker(pi|_{G_{E,p^2}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^2
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod p^2
	Y := Y1/Y2; // Magma will not reduce this mod p^2, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*p, 2*d*p, 1]; // Y := Y1/Y2 reduces to this matrix mod p^2
	print "This matrix reduces mod p^2 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod p. Y above reduces to the identity matrix mod p 
	print "Note that this is the identity matrix mod p.";
	print "==================";
	//Induction:
	// Let c = p^n.
	print "Induction (mod p^(n+1)): Let c = p^n.";
	A:=G![-1,0,0,1]; // mod p^{n+1}
	B:=G![a,b,d*b,a]; // mod p^{n+1}
	K:=G![1,c,d*c,1]; // mod p^{n+1}. K is an element of ker(pi|_{G_{E,p^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod p^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod p^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*c, 2*c*d, 1]; // Y := Y1/Y2 reduces to this matrix mod p^{n+1}
	print "This matrix reduces mod p^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod p^n. Y above reduces to the identity matrix mod p^n
	print "Note that this is the identity matrix mod p^n.";
	print "==================";
end procedure;


//Function that verifies Theorem 1.2 for the index 2 case
procedure VerifyThm12Index2()
	print "==================";
	print "Verifying Theorem 1.2 for the index 2 case.";
	F<a,b,c,d,p>:=FunctionField(Rationals(),5);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod p^2):";
	A:=G![-1,0,0,1]; // mod p^2
	B:=G![1,1,d*1,1]; // mod p^2
	K:=G![1,p,d*p,1]; // mod p^2. K is an element of ker(pi|_{G_{E,p^2}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^2
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod p^2
	Y := Y1/Y2; // Magma will not reduce this mod p^2, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*p, 2*d*p, 1]; // Y := Y1/Y2 reduces to this matrix mod p^2
	print "This matrix reduces mod p^2 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod p. Y above reduces to the identity matrix mod p 
	print "Note that this is the identity matrix mod p.";
	print "==================";
	//Induction:
	// Let c = p^n.
	print "Induction (mod p^(n+1)): Let c = p^n.";
	A:=G![-1,0,0,1]; // mod p^{n+1}
	B:=G![1,1,d*1,1]; // mod p^{n+1}
	K:=G![1,c,d*c,1]; // mod p^{n+1}. K is an element of ker(pi|_{G_{E,p^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod p^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod p^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod p^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*c, 2*c*d, 1]; // Y := Y1/Y2 reduces to this matrix mod p^{n+1}
	print "This matrix reduces mod p^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod p^n. Y above reduces to the identity matrix mod p^n
	print "Note that this is the identity matrix mod p^n.";
	print "==================";
end procedure;



//////////////////////////////////////////////////////////////////////////////////////////


//These procedures verify the computations in Theorem 1.3. 


//Function that verifies Theorem 1.3 for the index 1 case
procedure VerifyThm13Index1()
	print "==================";
	print "Verifying Theorem 1.3 for the index 1 case.";
	F<a,b,c>:=FunctionField(Rationals(),3);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod 3^4):";
	A:=G![-1,0,0,1]; // mod 81
	B:=G![a,b,-3*b/4,a]; // mod 81
	K:=G![1,27,0,1]; // mod 81. K is an element of ker(pi|_{G_{E,81}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 81
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 81
	Y := Y1/Y2; // Magma will not reduce this mod 81, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, (54*a^2)/(a^2 + 3/4*b^2), 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 81
	print "This matrix reduces mod 81 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 27. Y above reduces to the identity matrix mod 27 
	print "Note that this is the identity matrix mod 27.";
	print "==================";
	//Induction:
	// Let c = 3^n.
	print "Induction (mod 3^(n+1)): Let c = 3^n.";
	A:=G![-1,0,0,1]; // mod 3^{n+1}
	B:=G![a,b,-3*b/4,a]; // mod 3^{n+1}
	K:=G![1,c,0,1]; // mod 3^{n+1}. K is an element of ker(pi|_{G_{E,3^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 3^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 3^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 3^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, (2*a^2*c)/(a^2 + 3/4*b^2), 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 3^{n+1}
	print "This matrix reduces mod 3^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 3^n. Y above reduces to the identity matrix mod 3^n
	print "Note that this is the identity matrix mod 3^n.";
	print "==================";
end procedure;


//Function that verifies Theorem 1.3 for the index 2 case
procedure VerifyThm13Index2()
	print "==================";
	print "Verifying Theorem 1.3 for the index 2 case.";
	F<a,b,c>:=FunctionField(Rationals(),3);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod 3^4):";
	A:=G![-1,0,0,1]; // mod 81
	B:=G![1,1,-3/4,1]; // mod 81
	K:=G![1,27,0,1]; // mod 81. K is an element of ker(pi|_{G_{E,81}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 81
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 81
	Y := Y1/Y2; // Magma will not reduce this mod 81, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 54, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 81
	print "This matrix reduces mod 81 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 27. Y above reduces to the identity matrix mod 27 
	print "Note that this is the identity matrix mod 27.";
	print "==================";
	//Induction:
	// Let c = 3^n.
	print "Induction (mod 3^(n+1)): Let c = 3^n.";
	A:=G![-1,0,0,1]; // mod 3^{n+1}
	B:=G![1,1,-3/4,1]; // mod 3^{n+1}
	K:=G![1,c,0,1]; // mod 3^{n+1}. K is an element of ker(pi|_{G_{E,3^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 3^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 3^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 3^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 11*c/7, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 3^{n+1}
	print "This matrix reduces mod 3^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 3^n. Y above reduces to the identity matrix mod 3^n
	print "Note that this is the identity matrix mod 3^n.";
	print "==================";
end procedure;


//Function that verifies Theorem 1.3 for the index 3 and 6 cases
procedure VerifyThm13Index3and6()
	print "==================";
	print "Verifying Theorem 1.3 for the index 3 and 6 cases.";
	F<a,b,c>:=FunctionField(Rationals(),3);
	G:=GL(2,F);
	print "==================";
	print "Image 1";
	print "==================";
	//Base case:
	print "Base case (mod 3^4):";
	A:=G![-1,0,0,1]; // mod 81
	B:=G![1,0,0,1]; // mod 81
	K:=G![1,27,0,1]; // mod 81. K is an element of ker(pi|_{G_{E,81}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 81
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 81
	Y := Y1/Y2; // Magma will not reduce this mod 81, so you have to look at it and reduce it yourself.
	Y;
	y := G![1,0,0,1]; // Let y = Y mod 27. Y above reduces to the identity matrix mod 27 
	print "Note that this is the identity matrix mod 27.";
	print "==================";
	//Induction:
	// Let c = 3^n.
	print "Induction (mod 3^(n+1)): Let c = 3^n.";
	A:=G![-1,0,0,1]; // mod 3^{n+1}
	B:=G![1,0,0,1]; // mod 81
	K:=G![1,c,0,1]; // mod 3^{n+1}. K is an element of ker(pi|_{G_{E,3^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 3^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 3^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 3^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	y := G![1,0,0,1]; // Let y = Y mod 3^n. Y above reduces to the identity matrix mod 3^n
	print "Note that this is the identity matrix mod 3^n.";
	print "==================";
	print "Image 2";
	print "==================";
	//Base case:
	print "Base case (mod 3^4):";
	A:=G![-1,0,0,1]; // mod 81
	B:=G![1,1,-3/4,1]; // mod 81
	K:=G![1,27,0,1]; // mod 81. K is an element of ker(pi|_{G_{E,81}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 81
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 81
	Y := Y1/Y2; // Magma will not reduce this mod 81, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 54, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 81
	print "This matrix reduces mod 81 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 27. Y above reduces to the identity matrix mod 27 
	print "Note that this is the identity matrix mod 27.";
	print "==================";
	//Induction:
	// Let c = 3^n.
	print "Induction (mod 3^(n+1)): Let c = 3^n.";
	A:=G![-1,0,0,1]; // mod 3^{n+1}
	B:=G![1,1,-3/4,1]; // mod 3^{n+1}
	K:=G![1,c,0,1]; // mod 3^{n+1}. K is an element of ker(pi|_{G_{E,3^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 3^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 3^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 3^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 11*c/7, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 3^{n+1}
	print "This matrix reduces mod 3^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 3^n. Y above reduces to the identity matrix mod 3^n
	print "Note that this is the identity matrix mod 3^n.";
	print "==================";
	print "Image 3";
	print "==================";
	//Base case:
	print "Base case (mod 3^4):";
	A:=G![-1,0,0,1]; // mod 81
	B:=G![-5/4,1/2,-3/8,-5/4]; // mod 81
	K:=G![1,27,0,1]; // mod 81. K is an element of ker(pi|_{G_{E,81}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 81
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 81
	Y := Y1/Y2; // Magma will not reduce this mod 81, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 54, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 81
	print "This matrix reduces mod 81 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 27. Y above reduces to the identity matrix mod 27 
	print "Note that this is the identity matrix mod 27.";
	print "==================";
	//Induction:
	// Let c = 3^n.
	print "Induction (mod 3^(n+1)): Let c = 3^n.";
	A:=G![-1,0,0,1]; // mod 3^{n+1}
	B:=G![-5/4,1/2,-3/8,-5/4]; // mod 81
	K:=G![1,c,0,1]; // mod 3^{n+1}. K is an element of ker(pi|_{G_{E,3^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 3^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 3^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 3^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 53*c/28, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 3^{n+1}
	print "This matrix reduces mod 3^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 3^n. Y above reduces to the identity matrix mod 3^n
	print "Note that this is the identity matrix mod 3^n.";
	print "==================";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////

//These procedures verify Proposition 5.3.


//Function that verifies Prop. 5.3 for the split Cartan case
procedure VerifyProp53Split()
	print "==================";
	print "Verifying Proposition 5.3 for the split Cartan case.";
	F<a,b,c,d>:=FunctionField(Rationals(),4);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![-1,0,1,1]; // mod 32
	B:=G![2,1,-2,1]; // B:=G![a+b,b,-2*b,a]; // mod 32
	K:=G![1,16,0,17]; // mod 32. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![17, 16, 0, 17]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^n.
	print "Induction (mod 2^(n+1)): Let c = 2^n.";
	A:=G![-1,0,1,1]; // mod 2^{n+1}
	B:=G![2,1,-2,1]; // B:=G![a+b,b,-2*b,a]; // mod 2^{n+1}
	K:=G![1,c,0,1+c]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![c+1, c/(c+1), 0, c+1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
end procedure;


//Function that verifies Prop. 5.3 for the non-split Cartan case
procedure VerifyProp53NonSplit()
	print "==================";
	print "Verifying Proposition 5.3 for the non-split Cartan case.";
	F<a,b,c,d>:=FunctionField(Rationals(),4);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![-1,0,1,1]; // mod 32
	B:=G![1,0,0,1]; // B:=G![a+b,b,-3*b,a]; // mod 32
	K:=G![1,16,-3*16,17]; // mod 32. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![17, 0, 0, 17]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^n.
	print "Induction (mod 2^(n+1)): Let c = 2^n.";
	A:=G![-1,0,1,1]; // mod 2^{n+1}
	B:=G![1,0,0,1]; // B:=G![a+b,b,-3*b,a]; // mod 2^{n+1}
	K:=G![1,c,-3*c,1+c]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![c+1, 0, 0, c+1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////

//These procedures verify Proposition 5.4.


//Function that verifies Prop. 5.4 for the index 1 case
procedure VerifyProp54Index1()
	print "==================";
	print "Verifying Proposition 5.4 for the index 1 case.";
	F<a,b,c>:=FunctionField(Rationals(),3);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![0,1,1,0]; // mod 32
	B:=G![2,1,-1,1]; // mod 32
	K:=G![1,16,-16,17]; // mod 81. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![17, 0, 0, 17]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^n.
	print "Induction (mod 2^(n+1)): Let c = 2^n.";
	A:=G![0,1,1,0]; // mod 2^{n+1}
	B:=G![2,1,-1,1]; // mod 2^{n+1}
	K:=G![1,c,-c,1+c]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![c+1, 0, 0, c+1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
end procedure;


//Function that verifies Prop. 5.4 for the index 3 case
procedure VerifyProp54Index3()
	print "==================";
	print "Verifying Proposition 5.4 for the index 3 case.";
	F<a,b,c>:=FunctionField(Rationals(),3);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![0,1,1,0]; // mod 32
	B:=G![3,6,-6,3]; // mod 32
	K:=G![1,16,-16,17]; // mod 81. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![17, 0, 0, 17]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^n.
	print "Induction (mod 2^(n+1)): Let c = 2^n.";
	A:=G![0,1,1,0]; // mod 2^{n+1}
	B:=G![3,6,-6,3]; // mod 2^{n+1}
	K:=G![1,c,-c,1+c]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![c+1, 0, 0, c+1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////

//This procedure verifies Theorem 1.4.(b).(i).


//Function that verifies Theorem 1.4.(b).(i) for Delta_Kf^2 = -12 and -28
procedure VerifyThm14bi()
	F<a,b,c,d>:=FunctionField(Rationals(),4);
	G:=GL(2,F);
	print "==================";
	print "Verifying Theorem 1.4.(b).(i) for Delta_Kf^2 = -12.";
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![-1,0,0,1]; // mod 32
	B:=G![a,b,-3*b,a]; // mod 32
	K:=G![1,8,-24,1]; // mod 81. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1,16,16,1]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^{n-1}.
	print "Induction (mod 2^(n+1)): Let c = 2^(n-1).";
	A:=G![-1,0,0,1]; // mod 2^{n+1}
	B:=G![a,b,-3*b,a]; // mod 2^{n+1}
	K:=G![1,c,-3*c,1]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*c, -3*2*c, 1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
	print "Verifying Theorem 1.4.(b).(i) for Delta_Kf^2 = -28.";
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![-1,0,0,1]; // mod 32
	B:=G![a,b,-7*b,a]; // mod 32
	K:=G![1,8,-7*8,1]; // mod 81. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1,16,16,1]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^{n-1}.
	print "Induction (mod 2^(n+1)): Let c = 2^(n-1).";
	A:=G![-1,0,0,1]; // mod 2^{n+1}
	B:=G![a,b,-7*b,a]; // mod 2^{n+1}
	K:=G![1,c,-7*c,1]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*c, -7*2*c, 1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////

//These procedures verify Theorem 1.4.(b).(ii).


//Function that verifies Theorem 1.4.(b).(ii) for the index 1, 2, and 4 cases
procedure VerifyThm14bii()
	print "==================";
	print "Verifying Theorem 1.4.(b).(ii) for the index 1, 2, and 4 cases.";
	F<a,b,c,d>:=FunctionField(Rationals(),4);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![-1,0,0,1]; // mod 32
	//Note that you get the same results with all four choices of gamma'.
	B:=G![a,b,-b,a]; // mod 32
	K:=G![1,8,-8,1]; // mod 32. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1,16,16,1]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^{n-1}.
	print "Induction (mod 2^(n+1)): Let c = 2^(n-1).";
	A:=G![-1,0,0,1]; // mod 2^{n+1}
	//Note that you get the same results with all four choices of gamma'.
	B:=G![a,b,-b,a]; // mod 2^{n+1}
	K:=G![1,c,-c,1]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*c, -2*c, 1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////

//These procedures verify Theorem 1.4.(b).(iii).


//Function that verifies Theorem 1.4.(b).(iii) for the index 1 case
procedure VerifyThm14biiiIndex1()
	print "==================";
	print "Verifying Theorem 1.4.(b).(iii) for the index 1 case when Delta_Kf^2 = -8 or -16.";
	F<a,b,c,d>:=FunctionField(Rationals(),4);
	G:=GL(2,F);
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![-1,0,0,1]; // mod 32
	//Note that you get the same results with all four choices of gamma'.
	B:=G![a,b,d*b,a]; // mod 32
	K:=G![1,8,d*8,1]; // mod 32. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1,16,0,1]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^{n-1}.
	print "Induction (mod 2^(n+1)): Let c = 2^(n-1).";
	A:=G![-1,0,0,1]; // mod 2^{n+1}
	//Note that you get the same results with all four choices of gamma'.
	B:=G![a,b,d*b,a]; // mod 2^{n+1}
	K:=G![1,c,d*c,1]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*c, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
end procedure;


//Function that verifies Theorem 1.4.(b).(iii) for the index 2 case for Delta_Kf^2 = -8 and -16
procedure VerifyThm14biiiIndex2()
	F<a,b,c,d>:=FunctionField(Rationals(),4);
	G:=GL(2,F);
	print "==================";
	print "Verifying Theorem 1.4.(b).(iii) for the index 2 case when Delta_Kf^2 = -8.";
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![-1,0,0,1]; // mod 32
	//Note that you get the same results with all possible images.
	B:=G![1,1,-2,1]; // mod 32
	K:=G![1,8,-2*8,1]; // mod 32. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1,16,0,1]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^{n-1}.
	print "Induction (mod 2^(n+1)): Let c = 2^(n-1).";
	A:=G![-1,0,0,1]; // mod 2^{n+1}
	//Note that you get the same results with all possible images.
	B:=G![1,1,-2,1]; // mod 2^{n+1}
	K:=G![1,c,-2*c,1]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*c, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
	print "Verifying Proposition 5.7 for the index 2 case when Delta_Kf^2 = -16.";
	print "==================";
	//Base case:
	print "Base case (mod 2^5):";
	A:=G![-1,0,0,1]; // mod 32
	//Note that you get the same results with all possible images.
	B:=G![1,1,-4,1]; // mod 32
	K:=G![1,8,-4*8,1]; // mod 32. K is an element of ker(pi|_{G_{E,32}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 32
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); // another commutator mod 32
	Y := Y1/Y2; // Magma will not reduce this mod 32, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1,16,0,1]; // Y := Y1/Y2 reduces to this matrix mod 32
	print "This matrix reduces mod 32 to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 16. Y above reduces to the identity matrix mod 16 
	print "Note that this is the identity matrix mod 16.";
	print "==================";
	//Induction:
	// Let c = 2^{n-1}.
	print "Induction (mod 2^(n+1)): Let c = 2^(n-1).";
	A:=G![-1,0,0,1]; // mod 2^{n+1}
	//Note that you get the same results with all possible images.
	B:=G![1,1,-4,1]; // mod 2^{n+1}
	K:=G![1,c,-4*c,1]; // mod 2^{n+1}. K is an element of ker(pi|_{G_{E,2^{n+1}}})
	Y1 := A*B*A^(-1)*B^(-1); // commutator mod 2^{n+1}
	A2:=A*K;
	B2:=B*K;
	Y2 := A2*B2*A2^(-1)*B2^(-1); //another commutator mod 2^{n+1}
	Y := Y1/Y2; // Magma will not reduce this mod 2^{n+1}, so you have to look at it and reduce it yourself.
	Y;
	Y := G![1, 2*c, 0, 1]; // Y := Y1/Y2 reduces to this matrix mod 2^{n+1}
	print "This matrix reduces mod 2^(n+1) to", Y;
	y := G![1,0,0,1]; // Let y = Y mod 2^n. Y above reduces to the identity matrix mod 2^n
	print "Note that this is the identity matrix mod 2^n.";
	print "==================";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////

//The following procedure constitutes the proof of Lemma 5.2

//Proof of Lemma 5.2
procedure VerifyLemma52()
	print "======================================================";
	print "Verifying Lemma 5.2";
	print "======================================================";

	GL16 := GL(2,Integers(16));

	// Delta_Kf^2 = −11, −19, −27, −43, −67, and −163.

	N11 := GL2CartanNormalizer(-11,16); // delta = -3, phi = 1
	N19 := GL2CartanNormalizer(-19,16); // delta = -5, phi = 1
	N27 := GL2CartanNormalizer(-27,16); // delta = -3, phi = 3
	N43 := GL2CartanNormalizer(-43,16); // delta = -11, phi = 1
	N67 := GL2CartanNormalizer(-67,16); // delta = -17, phi = 1
	N163 := GL2CartanNormalizer(-163,16); // delta = -41, phi = 1

	// Let p=2 and let N11 be the normalizer of Cartan with Delta_Kf^2 = -11
	
	bool, conjugate := IsConjugate(GL16, N11, N19); // true [5, 3, 0, 1]
	print "Is N11 conjugate to N19?", bool;
	print "by", conjugate;  

	bool, conjugate := IsConjugate(GL16, N11, N27); // true [5, 6, 0, 1]
	print "Is N11 conjugate to N27?", bool;
	print "by", conjugate;  

	bool, conjugate := IsConjugate(GL16, N11, N43); // true [9, 8, 0, 1]
	print "Is N11 conjugate to N43?", bool;
	print "by", conjugate;  

	bool, conjugate := IsConjugate(GL16, N11, N67); // true [9, 15, 0, 1]
	print "Is N11 conjugate to N67?", bool;
	print "by", conjugate; 

	bool, conjugate := IsConjugate(GL16, N11, N163); // true [1, 7, 0, 1]
	print "Is N11 conjugate to N163?", bool;
	print "by", conjugate;  


	bool, conjugate := IsConjugate(GL16, N19, N27); // true [15, 12, 0, 1]
	print "Is N19 conjugate to N27?", bool;
	print "by", conjugate;  

	bool, conjugate := IsConjugate(GL16, N19, N43); // true [11, 2, 0, 1]
	print "Is N19 conjugate to N43?", bool;
	print "by", conjugate;  

	bool, conjugate := IsConjugate(GL16, N19, N67); // true [11, 7, 0, 1]
	print "Is N19 conjugate to N67?", bool;
	print "by", conjugate;  

	bool, conjugate := IsConjugate(GL16, N19, N163); // true [3, 15, 0, 1]
	print "Is N19 conjugate to N163?", bool;
	print "by", conjugate;  


	bool, conjugate := IsConjugate(GL16, N27, N43); // true [5, 10, 0, 1]
	print "Is N27 conjugate to N43?", bool;
	print "by", conjugate;  

	bool, conjugate := IsConjugate(GL16, N27, N67); // true [5, 5, 0, 1]
	print "Is N27 conjugate to N67?", bool;
	print "by", conjugate; 

	bool, conjugate := IsConjugate(GL16, N27, N163); // true [13, 13, 0, 1]
	print "Is N27 conjugate to N163?", bool;
	print "by", conjugate; 


	bool, conjugate := IsConjugate(GL16, N43, N67); // true [1, 15, 0, 1]
	print "Is N43 conjugate to N67?", bool;
	print "by", conjugate; 

	bool, conjugate := IsConjugate(GL16, N43, N163); // true [9, 7, 0, 1]
	print "Is N43 conjugate to N163?", bool;
	print "by", conjugate; 


	bool, conjugate := IsConjugate(GL16, N67, N163); // true [9, 8, 0, 1]
	print "Is N67 conjugate to N163?", bool;
	print "by", conjugate; 

	print "======================================================";
	print "Verified Lemma 5.2";
    print "======================================================";

end procedure; 


//////////////////////////////////////////////////////////////////////////////////////////

procedure VerifyAllComputations()
	print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print "%%%%%      Verifying all computations...       %%%%%";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print " ";
    print " ";
    print "======================================================";
	print "Verifying computations in Theorem 1.1";
    VerifyThm11SplitIndex1Cases();
    VerifyThm11NonSplitIndex1Cases();
    VerifyThm11SplitIndex3Case();
    VerifyThm11NonSplitIndex3Case();
    print "Verified computations in Theorem 1.1 ";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying computations in Theorem 1.2";
    VerifyThm12Index1();
    VerifyThm12Index2();
    print "Verified computations in Theorem 1.2 ";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying computations in Theorem 1.3";
    VerifyThm13Index1();
    VerifyThm13Index2();
    VerifyThm13Index3and6();
    print "Verified computations in Theorem 1.3";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Proposition 5.3";
    VerifyProp53Split();
    VerifyProp53NonSplit();
	print "Verified Proposition 5.3";
	print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Proposition 5.4";
    VerifyProp54Index1();
    VerifyProp54Index3();
    print "Verified Proposition 5.4";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Theorem 1.4.(b).(i)";
    VerifyThm14bi();
    print "Verified Theorem 1.4.(b).(i)";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Theorem 1.4.(b).(ii)";
    VerifyThm14bii();
    print "Verified Theorem 1.4.(b).(ii)";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Theorem 1.4.(b).(iii)";
    VerifyThm14biiiIndex1();
    VerifyThm14biiiIndex2();
    print "Verified Theorem 1.4.(b).(iii)";
    print "======================================================";
    print " ";
    print " ";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print "%%%%% All computations have been verified. %%%%%";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////


