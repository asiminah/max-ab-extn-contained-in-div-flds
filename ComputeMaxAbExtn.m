/*
	This code is for the paper "The maximal abelian extension contained in a division field of an elliptic curve over Q with complex multiplication" by Asimina S. Hamakiotes

	You are welcome to use and/or modify this code or any later version (but please be sure to cite the paper).
*/


/*
This code requires loading the databases of groups from: 
	http://users.wfu.edu/rouseja/2adic/gl2data.gz 
or alternatively:
	https://github.com/AndrewVSutherland/ell-adic-galois-images/tree/main/groups
*/


//Load the databases from RZB
load "gl2data.m";


print " ";
print "Run VerifyAllExamples() in order to verify all of the examples in Section 2 of the paper";
print " ";


//////////////////////////////////////////////////////////////////////////////////////////

// These are the elliptic curves in Table 1 of the paper, written in the form ED_f. 

E3_1 := EllipticCurve([0,16]);
E3_2 := EllipticCurve([-15,22]);
E3_3 := EllipticCurve([-480, 4048]);
E4_1 := EllipticCurve([1,0]);
E4_2 := EllipticCurve([-11,14]);
E7_1 := EllipticCurve([-1715,33614]);
E7_2 := EllipticCurve([-29155,1915998]);
E8_1 := EllipticCurve([-4320,96768]);
E11_1 := EllipticCurve([-9504,365904]);
E19_1 := EllipticCurve([-608,5776]);
E43_1 := EllipticCurve([-13760,621264]);
E67_1 := EllipticCurve([-117920,15585808]);
E163_1 := EllipticCurve([-34790720,78984748304]);

SimplestCMCurves := [E3_1, E3_2, E3_3, E4_1, E4_2, E7_1, E7_2, E8_1, E11_1, E19_1, E43_1, E67_1, E163_1];


//////////////////////////////////////////////////////////////////////////////////////////

//This function determines the twisting factor alpha of an elliptic curve over Q with CM that gives a simplest CM curve
//Input: an elliptic curve E/Q with CM
//Output: the twisting factor alpha and the simplest CM curve ED_f/Q with the same CM discriminant as E

ComputeTwist := function(E1)
	E1HasCM, E1disc := HasComplexMultiplication(E1);

	SimplestCMCurves := [E3_1, E3_2, E3_3, E4_1, E4_2, E7_1, E7_2, E8_1, E11_1, E19_1, E43_1, E67_1, E163_1];

	// This finds the curve in Table 1 of the paper that has the same CM disc as E1
	for i in [1..13] do
		E2HasCM, E2disc := HasComplexMultiplication(SimplestCMCurves[i]);
		if E1disc eq E2disc then
			E2 := SimplestCMCurves[i];
		end if;
	end for;

	E1 := WeierstrassModel(E1);

	//This computes alpha for j not 0,1728
	if (E1disc ne -3) and (E1disc ne -4) then
		A1 := Coefficients(E1)[4];
		B1 := Coefficients(E1)[5];
		A2 := Coefficients(E2)[4];
		B2 := Coefficients(E2)[5];
		A := A1/A2;
		B := B1/B2; 
		bool, alpha := IsSquare(A);
		if B le 0 then
			alpha := alpha *-1;
		end if; 
		if Denominator(alpha) ne 1 then
			alpha := alpha * Denominator(alpha)^2;
		end if; 
	end if; 

	//This computes alpha for j=0
	if (E1disc eq -3) then 
		B1 := Coefficients(E1)[5];
		B2 := Coefficients(E2)[5];
		alpha := B1/B2; // This is just B1/16 because B2 = 16
		if Denominator(alpha) ne 1 then
			alpha := alpha * 2^6;
		end if; 
	end if; 

	//This computes alpha for j=1728
	if (E1disc eq -4) then 
		A1 := Coefficients(E1)[4];
		A2 := Coefficients(E2)[4];
		alpha := A1/A2; // This is just A1 because A2 = 1
	end if; 

	return alpha, E2;
end function;


//////////////////////////////////////////////////////////////////////////////////////////

//This function takes an elliptic curve E/Q
//Returns [d,f], where d=discriminant of the maximal order, and f=conductor of the order End(E). 
 
CMdf := function(E)
	yesno,disc:=HasComplexMultiplication(E);
	if yesno eq false then
		print "The elliptic curve has no CM";
		return yesno,[];
	else
	x,y:=SquarefreeFactorization(disc);
	if x eq -1 then
		d:=-4;
		f:=y div 2;
	else
	if x eq -2 then
		d:=-8;
		f:=1;
	else
		d:=x;
		f:=y;
	end if;
	end if;
	// print "Elliptic curve has CM by an order with d=",d,", and conductor f=",f;
	return yesno,[d,f];
	end if;
end function;


//////////////////////////////////////////////////////////////////////////////////////////

//This function determines the maximal abelian extension. 
//Input: an elliptic curve E/Q with CM, a prime p
//Output: the maximal abelian extension contained in Q(E[p^n])/Q for n >= 2

MaxAbExtn := function(E,p)
	G := GL2CMEllAdicImage(E,p);
	bool, dfvec := CMdf(E);
	d := dfvec[1];
	f := dfvec[2];
	alpha, simplestCMCurve := ComputeTwist(E);
	alpha := Integers()!alpha;
	alphaReduced, sq := SquareFree(alpha);

	
	if alpha eq 1 then
		print "This is a simplest CM curve.";
	end if;

	if (p ne 2) and (p ne 3) then
		N := GL2CartanNormalizer(d*f^2,p);
		if d*f^2 mod p ne 0 then
			return "The maximal abelian extension is K(zeta_",p,"^n) = Q(",d,", zeta_",p,"^n).";
		else 
			if #N/#G eq 1 then
				return "The maximal abelian extension is Q(zeta_",p,"^n, sqrt(",alphaReduced,")).";
			else if #N/#G eq 2 then
				return "The maximal abelian extension is Q(zeta_",p,"^n).";
			end if;
			end if;
		end if;
	end if;


	if p eq 3 then
		N := GL2CartanNormalizer(d*f^2,p^3);
		if d*f^2 mod p ne 0 then
			return "The maximal abelian extension is K(zeta_",p,"^n) = Q(",d,", zeta_",p,"^n).";
		else
			if #N/#G in [1,3] then
				return "The maximal abelian extension is Q(zeta_",p,"^n, sqrt(",alphaReduced,")).";
			else if #N/#G in [2,6] then
				return "The maximal abelian extension is Q(zeta_",p,"^n).";
			end if;
			end if;
		end if;
	end if; 


	if p eq 2 then
		N := GL2CartanNormalizer(d*f^2,p^4);
		if d*f^2 mod p ne 0 then
			return "The maximal abelian extension is K(zeta_",p,"^n) = Q(",d,", zeta_",p,"^n).";
		else if d*f^2 in [-12,-28] then
			return "The maximal abelian extension is K(zeta_",p,"^(n+1)) = Q(",d,", zeta_",p,"^(n+1)).";
		else if d*f^2 eq -4 then
				if #N/#G in [1,2] then
					if (alphaReduced eq 1) or (alphaReduced eq -1) then 
						return "The maximal abelian extension is Q(zeta_",p,"^(n+1), sqrt(",alphaReduced*sq,"))."; 
					else 
						return "The maximal abelian extension is Q(zeta_",p,"^(n+1), sqrt(",alphaReduced,")).";
					end if; 
				else if #N/#G eq 4 then
					return "The maximal abelian extension is Q(zeta_",p,"^(n+1)).";
				end if;
				end if;
		else if d*f^2 in [-8,-16] then
				if #N/#G eq 1 then
					return "The maximal abelian extension is Q(zeta_",p,"^(n+1), sqrt(",alphaReduced,")).";
				else if #N/#G eq 2 then
					return "The maximal abelian extension is Q(zeta_",p,"^(n+1)).";
				end if;
				end if;
		end if;
		end if;
		end if;
		end if;
	end if;

	return 0;
end function;


//////////////////////////////////////////////////////////////////////////////////////////

//These procedures verify the examples in Section 2 of the paper. 


//Function that verifies Example 2.1. 
procedure VerifyExample21()
	print "==================";
	E := EllipticCurve([0, 0, 0, -35, 98]);
	E; 
	alpha, simplestCMCurve := ComputeTwist(E);
	print "alpha =", alpha;
	MaxAbExtn(E,5);
	print "==================";
end procedure;


//Function that verifies Example 2.2. 
procedure VerifyExample22()
	print "==================";
	E := EllipticCurve([0, 0, 0, -140, -784]);
	E; 
	alpha, simplestCMCurve := ComputeTwist(E);
	print "alpha =", alpha;
	MaxAbExtn(E,7);
	print "==================";
	Ea := simplestCMCurve; 
	Ea;
	alpha, simplestCMCurve := ComputeTwist(Ea);
	print "alpha =", alpha;
	MaxAbExtn(Ea,7);
	print "==================";
end procedure;


//Function that verifies Example 2.3. 
procedure VerifyExample23()
	print "==================";
	E := EllipticCurve([0, 0, 0, 0, -6]);
	E; 
	alpha, simplestCMCurve := ComputeTwist(E);
	print "alpha =", alpha;
	MaxAbExtn(E,3);
	print "==================";
	Ea := simplestCMCurve;
	Ea;
	alpha, simplestCMCurve := ComputeTwist(Ea);
	print "alpha =", alpha;
	MaxAbExtn(Ea,3);
	print "==================";
end procedure;


//Function that verifies Example 2.4. 
procedure VerifyExample24()
	print "==================";
	E := EllipticCurve([0, -1, 1, -7, 10]);
	E; 
	alpha, simplestCMCurve := ComputeTwist(E);
	print "alpha =", alpha;
	MaxAbExtn(E,2);
	print "==================";
end procedure;


//Function that verifies Example 2.5. 
procedure VerifyExample25()
	print "==================";
	E := EllipticCurve([0, 0, 0, -15, 22]);
	E; 
	alpha, simplestCMCurve := ComputeTwist(E);
	print "alpha =", alpha;
	MaxAbExtn(E,2);
	print "==================";
end procedure;


//Function that verifies Example 2.6. 
procedure VerifyExample26()
	print "==================";
	E := EllipticCurve([0, 0, 0, -9, 0]);
	E; 
	alpha, simplestCMCurve := ComputeTwist(E);
	print "alpha =", alpha;
	MaxAbExtn(E,2);
	print "==================";
	Ea := simplestCMCurve;
	Ea;
	alpha, simplestCMCurve := ComputeTwist(Ea);
	print "alpha =", alpha;
	MaxAbExtn(Ea,2);
	print "==================";
end procedure;


//Function that verifies Example 2.7.
procedure VerifyExample27()
	print "==================";
	E := EllipticCurve([0, 0, 0, -30, 56]);
	E; 
	alpha, simplestCMCurve := ComputeTwist(E);
	print "alpha =", alpha;
	MaxAbExtn(E,2);
	print "==================";
	Ea := simplestCMCurve;
	Ea;
	alpha, simplestCMCurve := ComputeTwist(Ea);
	print "alpha =", alpha;
	MaxAbExtn(Ea,2);
	print "==================";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////


procedure VerifyAllExamples()
	print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print "%%%%%      Verifying all examples...       %%%%%";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print " ";
    print " ";
    print "======================================================";
	print "Verifying Example 2.1";
	VerifyExample21();
    print "Verified Example 2.1";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Example 2.2";
    VerifyExample22();
    print "Verified Example 2.2";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Example 2.3";
    VerifyExample23();
    print "Verified Example 2.3";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Example 2.4";
    VerifyExample24();
    print "Verified Example 2.4";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Example 2.5";
    VerifyExample25();
    print "Verified Example 2.5";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Example 2.6";
    VerifyExample26();
    print "Verified Example 2.6";
    print "======================================================";
    print " ";
    print " ";
    print " ";
    print "======================================================";
    print "Verifying Example 2.7";
    VerifyExample27();
    print "Verified Example 2.7";
    print "======================================================";
    print " ";
    print " ";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
    print "%%%%% All examples have been verified. %%%%%";
    print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%";
end procedure;


//////////////////////////////////////////////////////////////////////////////////////////






