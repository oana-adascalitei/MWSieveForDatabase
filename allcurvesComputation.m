//compute set of known points, QC primes
//compute information from generators(J);
//compute projE1E2
load "NewFunctions.m";
load "allcurves.m";
load "MWSieveCode.m";
load "FindPrimes.m";

pts := [*[]: index in [1..#allcurves]*];
projE1E2 := [ [[],[]] : i in [1..#allcurves] ];
gens := [ [[],[]] : i in [1..#allcurves] ];
tor_bas := [[]: i in [1..#allcurves]];
tor_ord := [[]: i in [1..#allcurves]];
qc_pr := [[]: i in [1..#allcurves]];
for index in [1..#allcurves] do
  print "Curve",index;
  X := HyperellipticCurve(allcurves[index]);
  points := Points(X : Bound:=10000);
  points := Setseq(points);
  pts[index] := points;
  //if there is a rational Weiestrass point then we have bad disks
  if  #Roots(allcurves[index]) ge 1 then
    pr:=find_qc_primes(HyperellipticCurve(allcurves[index]): number_of_bad_disks:=2);
  else 
    try 
      pr := find_qc_primes(X);
    catch e
      print "there are bad disks"; 
      try 
        pr:=find_qc_primes(HyperellipticCurve(allcurves[index]): number_of_bad_disks:=2);
      catch e
        print "no QC primes"; 
      end try;
    end try;
  qc_pr[index] := [pr[1],pr[2],pr[3]];
  print qc_pr[index];
  end if;
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