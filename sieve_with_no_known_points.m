///////////////////////////////////////////////////////////////////
//																 //
// Let X be a genus 2 bielliptic curve over Q, with no known     //
// point in X(Q).                                                //
//                                                               //
// This is a simple sieve to show that X(Q) = empty set.         //
//                                                               //
///////////////////////////////////////////////////////////////////

/*
Based on [S15, Example 8.3]. 
Also uses functions from [S09] (MakeLookup1, MakeDLp1, MakeDL).

The main function is SimpleSieveBielliptic(X:lower_bound:=2, upper_bound:=500)
--> X a bielliptic genus 2 curve over Q;
--> lower_bound: lower bound for prime used for sieving;
--> upper_bound: upper bound for prime used for sieving.


We have phi: X -> E1 x E2, for some elliptic curves E1, E2 /Q.
Checks if for some good prime p such that lower_bound <= p <= upper_bound, 
phi(X(F_p)) and red_p(E_1(Q) x E_2(Q)) are disjoint.


Used it in the following examples:
//Example 1:
R<x> := PolynomialRing(Rationals());
f := 21*x^6 + 246*x^4 + 961*x^2 + 1252;  //LMFDB label: 473256.a.946512.1
X := HyperellipticCurve(f);
SimpleSieveBielliptic(X);
//gives true 331 (meaning that the sieve was successful (true) at the prime 331) 

//Example 2
R<x> := PolynomialRing(Rationals());
f := 28*x^6 + 108*x^4 + 140*x^2 + 61;  //LMFDB label: 826672.a.826672.1
X := HyperellipticCurve(f);
SimpleSieveBielliptic(X);
//gives true 181 (meaning that the sieve was successful (true) at the prime 181) 


REFERENCES:
-[S15] S. Siksek,  "Chabauty and the Mordell-Weil sieve". 
 In Advances on superelliptic curves and their applications, 
 volume 41 of NATO Sci. Peace Secur. Ser. D Inf. Commun. Secur.,
 pages 194–224. IOS, Amsterdam, 2015.
-[S09] N. Bruin and M. Stoll, ‘MWSieve-new.m’, MAGMA code for 
 Mordell–Weil sieve computation, 2009. Electronic appendix to 
 `The Mordell–Weil sieve: proving non-existence of rational points on curves’, LMS
 J. Comput. Math. 13 (2010) 272–306,
*/

function MakeLookup1(G, m) //from [S09] 
  return pmap<Codomain(m) -> G| [<m(g), g> : g in G]>;
end function;

function MakeDLp1(G, m, p) //from [S09] 
  // G a p-group
  if #G le 25 then
    return MakeLookup1(G, m);
  end if;
  invs := Invariants(G);
  // printf "MakeDLp: Invariants(G) = %o\n", invs;
  pp := ExactQuotient(invs[#invs], p);
  if pp eq 1 then
    return MakeLookup1(G, m);
  end if;
  // printf "MakeDLp: pp = %o\n", pp;
  h := hom<G -> G | [pp*G.i : i in [1..#invs]]>;
  G1 := Image(h);
  // printf "MakeDLp: Invariants(Image(h)) = %o\n", Invariants(G1);
  m1 := map<G1 -> Codomain(m) | x:->m(x)>;
  f1 := MakeLookup1(G1, m1);
  G2 := Kernel(h);
  // printf "MakeDLp: Invariants(Kernel(h)) = %o\n", Invariants(G2);
  m2 := map<G2 -> Codomain(m) | x:->m(x)>;
  f2 := MakeDLp1(G2, m2, p);
  return pmap<Codomain(m) -> G |
               x :-> f2(x - m(a)) + a where a := f1(pp*x) @@ h>;
end function;

function MakeDL(G, m)  //from [S09] 
// Given bijection  m : G -> X, where X has group structure, compute the
//  inverse of m. Assumes that #G is smooth.
  n := #Invariants(G);
  f := Factorization(#G);
  cofs := [&*[Integers()|f[i,1]^f[i,2] : i in [1..#f] | i ne j] : j in [1..#f]];
  _, refs := XGCD(cofs);
  assert &+[Integers()|refs[i]*cofs[i] : i in [1..#f]] eq 1;
  DLs := [**];
  for i := 1 to #f do
    p := f[i,1];
    hp := hom<G -> G | [cofs[i]*G.j : j in [1..n]]>;
    Gp := Image(hp);
    mp := map<Gp -> Codomain(m) | x:->m(x)>;
    DLp := MakeDLp1(Gp, mp, p);
    Append(~DLs, DLp);
  end for;
  return pmap<Codomain(m) -> G
               | x :-> &+[G|refs[i]*G!(DLs[i](cofs[i]*x)) : i in [1..#f]]>;
end function;

function SimpleSieveBielliptic(X:lower_bound:=2, upper_bound:=500)
	
	X := SimplifiedModel(X);
	subcovs := Degree2Subcovers(X);
	assert #subcovs ge 2;
	E1,phi1 := Explode(subcovs[1]);
	E2,phi2 := Explode(subcovs[2]);
	pols1 := DefiningPolynomials(phi1);
	pols2 := DefiningPolynomials(phi2);
	
	Bad := BadPrimes(X);
	primes := [p : p in [lower_bound..upper_bound] | IsPrime(p)];
	GoodPrimes := [p : p  in primes | p notin Bad];

	Gens1, bl11, bl12 := Generators(E1);
	assert bl11 eq true; assert bl12 eq true;
	Gens2, bl21, bl22 := Generators(E2);
	assert bl21 eq true; assert bl22 eq true;

	success := false;
	successfulp := 0;
	for p in GoodPrimes do
		Xp := ChangeRing(X, GF(p));
		E1p := ChangeRing(E1, GF(p));
		E2p := ChangeRing(E2, GF(p));
		pols1p := [* ChangeRing(P, GF(p)) : P in pols1 *];
		pols1p := [Parent(pols1p[1]) | pols1p[i] : i in [1..#pols1p]];
		pols2p := [Parent(pols1p[1]) | ChangeRing(P, GF(p)) : P in pols2];
		phi1p := map< Xp -> E1p | pols1p >;
		phi2p := map< Xp -> E2p | pols2p >;
		
		A1p, m1:= AbelianGroup(E1p);
		A2p, m2 := AbelianGroup(E2p);
		DL1 := MakeDL(A1p, m1);
		DL2 := MakeDL(A2p, m2);
		A, i1, i2:=DirectSum(A1p,A2p);
		imC := [i1(DL1(phi1p(Q))) + i2(DL2(phi2p(Q))) : Q in Points(Xp)];
		imbas1 := [i1(DL1(E1p!P)) : P in Gens1];
		imbas2 := [i2(DL2(E2p!P)) : P in Gens2];
		imbas := imbas1 cat imbas2;
		imE1QE2Q := sub<A | imbas>;
		imCres := [ R : R in imE1QE2Q | R in imC];
		if #imCres eq 0 then
			successfulp := p;
			success := true;
			break p;
		end if;
	end for;
	
	return success, successfulp;
	
end function;