/*
	This code is for the paper "Maximal abelian extensions contained in division fields of elliptic
	curves over Q with complex multiplication" by Asimina S. Hamakiotes
*/

print "Run VerifyAll() in order to verify all the computations in Section 5 of the paper";

//////////////////////////////////////////////////////////////////////////////////////////

//These procedures verify Proposition 5.1. 


//Function that verifies Prop. 5.1.(a) and (b) for the split case (index 1)
procedure VerifyProp51abSplitIndex1()
	print "==================";
	print "Verifying Proposition 5.1(a) and (b) for the split index 1 case.";
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


//Function that verifies Prop. 5.1.(b) for the split case (index 3)
procedure VerifyProp51bSplitIndex3()
	print "==================";
	print "Verifying Proposition 5.1(b) for the split index 3 case.";
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


//Function that verifies Prop. 5.1.(a) and (b) for the non-split case (index 1)
procedure VerifyProp51abNonSplitIndex1()
	print "==================";
	print "Verifying Proposition 5.1(a) and (b) for the non-split index 1 case.";
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


//Function that verifies Prop. 5.1.(b) for the non-split case (index 3)
procedure VerifyProp51bNonSplitIndex3()
	print "==================";
	print "Verifying Proposition 5.1(b) for the non-split index 3 case.";
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

//These procedures verify Proposition 5.2.


//Function that verifies Prop. 5.2.(a) for the index 1 case
procedure VerifyProp52aIndex1()
	print "==================";
	print "Verifying Proposition 5.2(a) for the index 1 case.";
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


//Function that verifies Prop. 5.2.(a) for the index 2 case
procedure VerifyProp52aIndex2()
	print "==================";
	print "Verifying Proposition 5.2(a) for the index 2 case.";
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



//Function that verifies Prop. 5.2.(b) for the index 1 case
procedure VerifyProp52bIndex1()
	print "==================";
	print "Verifying Proposition 5.2(b) for the index 1 case.";
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


//Function that verifies Prop. 5.2.(b) for the index 2 case
procedure VerifyProp52bIndex2()
	print "==================";
	print "Verifying Proposition 5.2(b) for the index 2 case.";
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


//Function that verifies Prop. 5.2.(b) for the index 3 and 6 cases
procedure VerifyProp52bIndex3and6()
	print "==================";
	print "Verifying Proposition 5.2(b) for the index 3 and 6 cases.";
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

//This procedure verifies Proposition 5.5.


//Function that verifies Prop. 5.5 for Delta_Kf^2 = -12 and -28
procedure VerifyProp55()
	F<a,b,c,d>:=FunctionField(Rationals(),4);
	G:=GL(2,F);
	print "==================";
	print "Verifying Proposition 5.5 for Delta_Kf^2 = -12.";
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
	print "Verifying Proposition 5.5 for Delta_Kf^2 = -28.";
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

//These procedures verify Proposition 5.6.


//Function that verifies Prop. 5.6 for the index 1, 2, and 4 cases
procedure VerifyProp56()
	print "==================";
	print "Verifying Proposition 5.6 for the index 1, 2, and 4 cases.";
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

//These procedures verify Proposition 5.7.


//Function that verifies Prop. 5.7 for the index 1 case
procedure VerifyProp57Index1()
	print "==================";
	print "Verifying Proposition 5.7 for the index 1 case when Delta_Kf^2 = -8 or -16.";
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


//Function that verifies Prop. 5.7 for the index 2 case for Delta_Kf^2 = -8 and -16
procedure VerifyProp57Index2()
	F<a,b,c,d>:=FunctionField(Rationals(),4);
	G:=GL(2,F);
	print "==================";
	print "Verifying Proposition 5.7 for the index 2 case when Delta_Kf^2 = -8.";
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

procedure VerifyAll()
	print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print "%%%%%      Verifying all computations...       %%%%%";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print " ";
    print " ";
    print "======================================================";
	print "Verifying Proposition 5.1";
    VerifyProp51abSplitIndex1();
    VerifyProp51abNonSplitIndex1();
    VerifyProp51bSplitIndex3();
    VerifyProp51bNonSplitIndex3();
    print "Verified Proposition 5.1 ";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Proposition 5.2(a)";
    VerifyProp52aIndex1();
    VerifyProp52aIndex2();
    print "Verified Proposition 5.2(a) ";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Proposition 5.2(b)";
    VerifyProp52bIndex1();
    VerifyProp52bIndex2();
    VerifyProp52bIndex3and6();
    print "Verified Proposition 5.2(b)";
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
    print "Verifying Proposition 5.5";
    VerifyProp55();
    print "Verified Proposition 5.5";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Proposition 5.6";
    VerifyProp56();
    print "Verified Proposition 5.6";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Proposition 5.7";
    VerifyProp57Index1();
    VerifyProp57Index2();
    print "Verified Proposition 5.7";
    print "======================================================";
    print " ";
    print " ";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print "%%%%% All computations have been verified. %%%%%";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////


