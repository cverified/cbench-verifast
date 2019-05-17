/*@

predicate faculty(int n; int f) = n == 0 ? f == 1 : 1 <= n &*& faculty(n - 1, ?f0) &*& f == f0 * n;

lemma_auto void faculty_inv()
    requires faculty(?n, ?f);
    ensures faculty(n, f) &*& 0 <= n &*& 1 <= f;
{
    open faculty(n, f);
    if (n >= 1) {
        assert faculty(n - 1, ?f0);
        faculty_inv();
        mul_mono_l(1, n, f0);
    }
}

lemma void faculty_le(int n1, int n2)
    requires faculty(n1, ?f1) &*& faculty(n2, ?f2) &*& n1 >= n2;
    ensures faculty(n1, f1) &*& faculty(n2, f2) &*& f1 >= f2;
{
    if (n1 == n2) {
        merge_fractions faculty(n1, _);
    } else {
        open faculty(n1, f1);
        assert faculty(n1 - 1, ?f0);
        faculty_le(n1 - 1, n2);
        mul_mono_l(1, n1, f0);
    }
}

@*/

int fac(int n)
	//@ requires faculty(n, ?r) &*& n < INT_MAX &*& r <= INT_MAX;
	//@ ensures result == r;
	//@ terminates;
{
	int f = 1;
	for (int i = 1; i <= n; i++)
		//@ invariant faculty(n, r) &*& faculty(i - 1, f) &*& 1 <= i &*& i - 1 <= n;
		//@ decreases n - i;
	{
		//@ faculty_le(n, i);
		f = f * i;
	}
	//@ merge_fractions faculty(n, _);
	return f;
	//@ leak faculty(_, _) &*& faculty(_, _);
}
