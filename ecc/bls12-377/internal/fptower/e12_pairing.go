package fptower

func (z *E12) nSquare(n int) {
	for i := 0; i < n; i++ {
		z.CyclotomicSquare(z)
	}
}

func (z *E12) nSquareCompressed(n int) {
	for i := 0; i < n; i++ {
		z.CyclotomicSquareCompressed(z)
	}
}

// Expt set z to x^t in E12 and return z
func (z *E12) Expt(x *E12) *E12 {
	// const tAbsVal uint64 = 9586122913090633729
	// tAbsVal in binary: 1000010100001000110000000000000000000000000000000000000000000001
	// drop the low 46 bits (all 0 except the least significant bit): 	 = 136227
	// Shortest addition chains can be found at https://wwwhomes.uni-bielefeld.de/achim/addition_chain.html

	var result, x33 E12

	// a shortest addition chain for 136227 --> 17S, 4M instead of 18S, 5M
	result.Set(x)
	result.nSquare(5)
	result.Mul(&result, x)
	x33.Set(&result)
	result.nSquare(7)
	result.Mul(&result, &x33)
	result.nSquare(4)
	result.Mul(&result, x)
	result.CyclotomicSquare(&result)
	result.Mul(&result, x)

	// the remaining 46 bits
	result.nSquareCompressed(46)
	result.Decompress(&result)
	result.Mul(&result, x)

	z.Set(&result)
	return z
}

// 												  R1 R0   R2
// MulBy235 multiplication by sparse element (0,0,c2,c3,0,c5)
func (z *E12) MulBy245(c2, c3, c5 *E2) *E12 {

	var t1, t2 E2
	var res E12

	t1.Mul(c3, &z.C1.B1)
	t2.Mul(c2, &z.C0.B2)
	res.C0.B0.Mul(c5, &z.C1.B0).
		Add(&res.C0.B0, &t1).
		Add(&res.C0.B0, &t2).
		MulByNonResidue(&res.C0.B0)

	t1.Mul(c3, &z.C1.B2)
	t2.Mul(c5, &z.C1.B1)
	t1.Add(&t1, &t2).MulByNonResidue(&t1)
	res.C0.B1.Mul(c2, &z.C0.B0).
		Add(&res.C0.B1, &t1)

	t1.Mul(c3, &z.C1.B0)
	t2.Mul(c2, &z.C0.B1)
	res.C0.B2.Mul(c5, &z.C1.B2).
		MulByNonResidue(&res.C0.B2).
		Add(&res.C0.B2, &t1).
		Add(&res.C0.B2, &t2)

	t1.Mul(c3, &z.C0.B2)
	t2.Mul(c2, &z.C1.B2)
	res.C1.B0.Mul(c5, &z.C0.B1).
		Add(&res.C1.B0, &t1).
		Add(&res.C1.B0, &t2).
		MulByNonResidue(&res.C1.B0)

	t1.Mul(c3, &z.C0.B0)
	t2.Mul(c2, &z.C1.B0)
	res.C1.B1.Mul(c5, &z.C0.B2).
		MulByNonResidue(&res.C1.B1).
		Add(&res.C1.B1, &t1).
		Add(&res.C1.B1, &t2)

	t1.Mul(c3, &z.C0.B1)
	t2.Mul(c2, &z.C1.B1)
	res.C1.B2.Mul(c5, &z.C0.B0).
		Add(&res.C1.B2, &t1).
		Add(&res.C1.B2, &t2)

	z.Set(&res)

	return z
}

// MulBy034 multiplication by sparse element (c0,0,0,c3,c4,0)
func (z *E12) MulBy034(c0, c3, c4 *E2) *E12 {

	var a, b, d E6

	a.MulByE2(&z.C0, c0)

	b.Set(&z.C1)
	b.MulBy01(c3, c4)

	c0.Add(c0, c3)
	d.Add(&z.C0, &z.C1)
	d.MulBy01(c0, c4)

	z.C1.Add(&a, &b).Neg(&z.C1).Add(&z.C1, &d)
	z.C0.MulByNonResidue(&b).Add(&z.C0, &a)

	return z
}
