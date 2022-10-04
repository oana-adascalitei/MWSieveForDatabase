//compute torsion subgroups for all Jacobians

load "allcurves.m";

t1 := 0; t2 := 0; t3 := 0; t4 := 0; t5 := 0; t6 := 0;
T1 := []; T2 := []; T3 := []; T4 := []; T5 := []; T6 := [];

for index in [1..#all_fake_coeffs]  do
	X := HyperellipticCurve(allcurves[index]);
	J := Jacobian(X);
	T := TorsionSubgroup(J);

	if #T eq 1 then 
		t1 := t1+1;
    	T1 := T1 cat [index];
	end if;

	if #T eq 2 then 
		t2 := t2+1;
    	T2 := T2 cat [index];
	end if;

	if #T eq 3 then 
		t3 := t3+1;
		T3 := T3 cat [index];
	end if;

	if #T eq 4 then 
		t4 := t4+1;
		T4 := T4 cat [index];
	end if;

	if #T eq 5 then 
		t5 := t5+1;
		T5 := T5 cat [index];
	end if;

	if #T eq 6 then 
		t6 := t6+1;
		T6 := T6 cat [index];
	end if;

end for;

assert t1+t2+t3+t4+t5+t6 eq #all_fake_coeffs;