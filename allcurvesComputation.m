//compute set of known points
//compute information from generators(J);
//compute projE1E2
//compute three smallest primes of good ordinary reduction

load "NewFunctions.m";
load "allcurves.m";
load "MWSieveCode.m";
load "allcurvesOutput.m";

pts := [*[]: index in [1..#allcurves]*];
projE1E2 := [ [[],[]] : i in [1..#allcurves] ];
gens := [ [[],[]] : i in [1..#allcurves] ];
tor_bas := [[]: i in [1..#allcurves]];
tor_ord := [[]: i in [1..#allcurves]];
for index in [1..#allcurves] do
  print "Curve",index;
  X := HyperellipticCurve(allcurves[index]);
  points := Points(X : Bound:=10000);
  points := Setseq(points);
  pts[index] := points;
  J := Jacobian(X);
  torsion_bas, torsion_orders, bas:=generators(J);
  gens[index] := [Eltseq(bas[1]),Eltseq(bas[2])];
  tor_bas[index] := [Eltseq(torsion_bas[i]): i in [1..#torsion_bas]];
  tor_ord[index] := torsion_orders;
  P1 := elt< J | bas[1][1], bas[1][2], bas[1][3] >;
  P2 := elt< J | bas[2][1], bas[2][2], bas[2][3] >;
  [ellproj(P1),ellproj(P2)];
  projE1E2[index] := [ellproj(P1),ellproj(P2)];
end for;



ordinary_pr := [[]: i in [1..#allcurves]];
Primes := PrimesInInterval(3,100);

for i in [1..#allcurves] do
  i;
  X := HyperellipticCurve(allcurves[i]);
  D:=Degree2Subcovers(X);
  E1 := MinimalModel(D[1][1]);
  E2 := MinimalModel(D[2][1]);
  GoodPrimes := [p : p in Primes | p in BadPrimes(X) eq false];
  OP := [p : p in GoodPrimes | IsOrdinary(ChangeRing(E1,GF(p))) and IsOrdinary(ChangeRing(E2,GF(p)))];
  ordinary_pr[i] := [OP[1],OP[2],OP[3]];
end for;