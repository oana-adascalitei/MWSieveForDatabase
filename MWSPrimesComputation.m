//we pre-compute mws_primes with respect to aux_int = 1
//we do the same for aux_int = 2, aux_int = 4
load "MWSieveCode.m";
load "allcurvesOutput.m";
load "allcurves.m";

MWSPrimes4 := [[]: index in [1..#allcurves]];
LowerBound := [115];
R<x> := PolynomialRing(Rationals());
N := 4; //exponent for all QC primes
ind := [1,2,3]; //indices
for index in [i : i in [1..#allcurves]| i in [295,333] eq false] do
    print("Curve"),index;
    print allcurves[index];
    ordinary_primes := [ordinary_pr[index][i] : i in ind ];
    print ordinary_primes;
    exponents := [N : p in ordinary_primes];
    X:=HyperellipticCurve(allcurves[index]);
    J:=Jacobian(X);
    B := BadPrimes(X); 
    AA := 10^4;
    if index in LowerBound then
        AA := 10^3;
    end if;
    A := PrimesUpTo(AA); 
    for v in B do
        A := Exclude(A,v);
    end for;
    groups := [];
    for i in [1..#A] do
        groups[i] := AbelianGroup(Jacobian(ChangeRing(X,GF(A[i]))));
    end for;
    qc_M := &*[ordinary_primes[i]^exponents[i] : i in [1..#ordinary_primes]];  
    aux_int := 4; //or aux_int := 2; or aux_int := 4;
    M := qc_M*aux_int; // modulus
    mws_primes := sieving_primes(M, A, groups, 0.5 : printlevel := 0); 
    print mws_primes;
    MWSPrimes4[index] := mws_primes;
end for;