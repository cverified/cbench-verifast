//@ #include "nat.gh"

/*@

lemma void note(bool b)
    requires b;
    ensures b;
{}

fixpoint int fac__(nat n) {
    switch (n) {
        case zero: return 1;
        case succ(n0): return int_of_nat(n) * fac__(n0);
    }
}

fixpoint int fac_(int n) { return fac__(nat_of_int(n)); }

lemma_auto void fac__positive(nat n)
    requires true;
    ensures 1 <= fac__(n);
{
    switch (n) {
        case zero:
        case succ(n0):
            fac__positive(n0);
            mul_mono_l(1, int_of_nat(n), fac__(n0));
    }
}

lemma void fac_le(int n1, int n2)
    requires 1 <= n1 &*& n1 <= n2;
    ensures fac_(n1) <= fac_(n2);
{
    for (int n = n1; n < n2; n++)
        invariant n1 <= n &*& n <= n2 &*& fac_(n1) <= fac_(n);
        decreases n2 - n;
    {
        mul_mono_l(1, n + 1, fac_(n));
        note(int_of_nat(succ(nat_of_int(n))) == n + 1);
    }
}

@*/

int fac(int n)
	//@ requires 0 <= n &*& n <= 12;
	//@ ensures result == fac_(n);
	//@ terminates;
{
	int f = 1;
	for (int i = 1; i <= n; i++)
		//@ invariant 1 <= i &*& i - 1 <= n &*& f == fac_(i - 1);
		//@ decreases n - i;
	{
		//@ fac_le(i, 12);
		//@ note(nat_of_int(i) == succ(nat_of_int(i - 1)));
		f = f * i;
	}
	return f;
}
