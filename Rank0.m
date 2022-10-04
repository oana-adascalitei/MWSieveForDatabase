//this function finds
//the Q-rational points of a genus 2 curve defined and bielliptic over Q with a rank 0 quotient

load "BiellipticGenus2List.m";

Rank0 := function(X : HypCrv)
RatPoints := [];
A := Automorphisms(X);
for j in [3..#A] do 
    if A[j]^2 eq A[1] then
        G := AutomorphismGroup(X,[A[j]]);
        Q,m := CurveQuotient(G);
        if Rank(Jacobian(Q)) eq 0 then
            pts := Points(Q: Bound:=1000);
            assert #pts eq #TorsionSubgroup(Jacobian(Q));
            for k in [1..#pts] do
                R := RationalPoints(Difference(Pullback(m,Q!pts[k]), BaseScheme(m)));
                S:=IndexedSetToSequence(R);
                RatPoints := RatPoints cat S;
            end for;
            break j;
        end if;
    end if;
end for;
return RatPoints;
end function;

//////////////////////

//Example
// _<x> := PolynomialRing(Rationals());
// X := HyperellipticCurve([x^4+x^2,x^3+1]);
// X;
// Rank0(X);

//Z contains the 59 bielliptic curves from the database which have a rank 0 quotient 

// for X in Z do
//     X;
//     Rank0(X);
//     print "--------";
// end for;