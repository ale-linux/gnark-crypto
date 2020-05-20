// Copyright 2020 ConsenSys AG
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Code generated by gurvy/internal/generators DO NOT EDIT

package bn256

import (
	"math/bits"

	"github.com/consensys/gurvy/bn256/fp"
)

// e12 is a degree-two finite field extension of fp6:
// C0 + C1w where w^3-v is irrep in fp6

// fp2, fp12 are both quadratic field extensions
// template code is duplicated in fp2, fp12
// TODO make an abstract quadratic extension template

type e12 struct {
	C0, C1 e6
}

// Equal compares two e12 elements
// TODO can this be deleted?
func (z *e12) Equal(x *e12) bool {
	return z.C0.Equal(&x.C0) && z.C1.Equal(&x.C1)
}

// String puts e12 in string form
func (z *e12) String() string {
	return (z.C0.String() + "+(" + z.C1.String() + ")*w")
}

// SetString sets a e12 from string
func (z *e12) SetString(s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11 string) *e12 {
	z.C0.SetString(s0, s1, s2, s3, s4, s5)
	z.C1.SetString(s6, s7, s8, s9, s10, s11)
	return z
}

// Set copies x into z and returns z
func (z *e12) Set(x *e12) *e12 {
	z.C0 = x.C0
	z.C1 = x.C1
	return z
}

// SetOne sets z to 1 in e12 in Montgomery form and returns z
func (z *e12) SetOne() *e12 {
	z.C0.B0.A0.SetOne()
	z.C0.B0.A1.SetZero()
	z.C0.B1.A0.SetZero()
	z.C0.B1.A1.SetZero()
	z.C0.B2.A0.SetZero()
	z.C0.B2.A1.SetZero()
	z.C1.B0.A0.SetZero()
	z.C1.B0.A1.SetZero()
	z.C1.B1.A0.SetZero()
	z.C1.B1.A1.SetZero()
	z.C1.B2.A0.SetZero()
	z.C1.B2.A1.SetZero()
	return z
}

// ToMont converts to Mont form
// TODO can this be deleted?
func (z *e12) ToMont() *e12 {
	z.C0.ToMont()
	z.C1.ToMont()
	return z
}

// FromMont converts from Mont form
// TODO can this be deleted?
func (z *e12) FromMont() *e12 {
	z.C0.FromMont()
	z.C1.FromMont()
	return z
}

// Add set z=x+y in e12 and return z
func (z *e12) Add(x, y *e12) *e12 {
	z.C0.Add(&x.C0, &y.C0)
	z.C1.Add(&x.C1, &y.C1)
	return z
}

// Sub set z=x-y in e12 and return z
func (z *e12) Sub(x, y *e12) *e12 {
	z.C0.Sub(&x.C0, &y.C0)
	z.C1.Sub(&x.C1, &y.C1)
	return z
}

// SetRandom used only in tests
// TODO eliminate this method!
func (z *e12) SetRandom() *e12 {
	z.C0.B0.A0.SetRandom()
	z.C0.B0.A1.SetRandom()
	z.C0.B1.A0.SetRandom()
	z.C0.B1.A1.SetRandom()
	z.C0.B2.A0.SetRandom()
	z.C0.B2.A1.SetRandom()
	z.C1.B0.A0.SetRandom()
	z.C1.B0.A1.SetRandom()
	z.C1.B1.A0.SetRandom()
	z.C1.B1.A1.SetRandom()
	z.C1.B2.A0.SetRandom()
	z.C1.B2.A1.SetRandom()
	return z
}

// Mul set z=x*y in e12 and return z
func (z *e12) Mul(x, y *e12) *e12 {
	// Algorithm 20 from https://eprint.iacr.org/2010/354.pdf

	var t0, t1, xSum, ySum e6

	t0.Mul(&x.C0, &y.C0) // step 1
	t1.Mul(&x.C1, &y.C1) // step 2

	// finish processing input in case z==x or y
	xSum.Add(&x.C0, &x.C1)
	ySum.Add(&y.C0, &y.C1)

	// step 3
	{ // begin: inline z.C0.MulByNonResidue(&t1)
		var result e6
		result.B1.Set(&(&t1).B0)
		result.B2.Set(&(&t1).B1)
		{ // begin: inline result.B0.MulByNonResidue(&(&t1).B2)
			var buf, buf9 e2
			buf.Set(&(&t1).B2)
			buf9.Double(&buf).
				Double(&buf9).
				Double(&buf9).
				Add(&buf9, &buf)
			result.B0.A1.Add(&buf.A0, &buf9.A1)
			{ // begin: inline MulByNonResidue(&(result.B0).A0, &buf.A1)
				(&(result.B0).A0).Neg(&buf.A1)
			} // end: inline MulByNonResidue(&(result.B0).A0, &buf.A1)
			result.B0.A0.AddAssign(&buf9.A0)
		} // end: inline result.B0.MulByNonResidue(&(&t1).B2)
		z.C0.Set(&result)
	} // end: inline z.C0.MulByNonResidue(&t1)
	z.C0.Add(&z.C0, &t0)

	// step 4
	z.C1.Mul(&xSum, &ySum).
		Sub(&z.C1, &t0).
		Sub(&z.C1, &t1)

	return z
}

// Square set z=x*x in e12 and return z
func (z *e12) Square(x *e12) *e12 {
	// TODO implement Algorithm 22 from https://eprint.iacr.org/2010/354.pdf
	// or the complex method from fp2
	// for now do it the dumb way
	var b0, b1 e6

	b0.Square(&x.C0)
	b1.Square(&x.C1)
	{ // begin: inline b1.MulByNonResidue(&b1)
		var result e6
		result.B1.Set(&(&b1).B0)
		result.B2.Set(&(&b1).B1)
		{ // begin: inline result.B0.MulByNonResidue(&(&b1).B2)
			var buf, buf9 e2
			buf.Set(&(&b1).B2)
			buf9.Double(&buf).
				Double(&buf9).
				Double(&buf9).
				Add(&buf9, &buf)
			result.B0.A1.Add(&buf.A0, &buf9.A1)
			{ // begin: inline MulByNonResidue(&(result.B0).A0, &buf.A1)
				(&(result.B0).A0).Neg(&buf.A1)
			} // end: inline MulByNonResidue(&(result.B0).A0, &buf.A1)
			result.B0.A0.AddAssign(&buf9.A0)
		} // end: inline result.B0.MulByNonResidue(&(&b1).B2)
		b1.Set(&result)
	} // end: inline b1.MulByNonResidue(&b1)
	b1.Add(&b0, &b1)

	z.C1.Mul(&x.C0, &x.C1).Double(&z.C1)
	z.C0 = b1

	return z
}

// Inverse set z to the inverse of x in e12 and return z
func (z *e12) Inverse(x *e12) *e12 {
	// Algorithm 23 from https://eprint.iacr.org/2010/354.pdf

	var t [2]e6

	t[0].Square(&x.C0) // step 1
	t[1].Square(&x.C1) // step 2
	{                  // step 3
		var buf e6
		{ // begin: inline buf.MulByNonResidue(&t[1])
			var result e6
			result.B1.Set(&(&t[1]).B0)
			result.B2.Set(&(&t[1]).B1)
			{ // begin: inline result.B0.MulByNonResidue(&(&t[1]).B2)
				var buf, buf9 e2
				buf.Set(&(&t[1]).B2)
				buf9.Double(&buf).
					Double(&buf9).
					Double(&buf9).
					Add(&buf9, &buf)
				result.B0.A1.Add(&buf.A0, &buf9.A1)
				{ // begin: inline MulByNonResidue(&(result.B0).A0, &buf.A1)
					(&(result.B0).A0).Neg(&buf.A1)
				} // end: inline MulByNonResidue(&(result.B0).A0, &buf.A1)
				result.B0.A0.AddAssign(&buf9.A0)
			} // end: inline result.B0.MulByNonResidue(&(&t[1]).B2)
			buf.Set(&result)
		} // end: inline buf.MulByNonResidue(&t[1])
		t[0].Sub(&t[0], &buf)
	}
	t[1].Inverse(&t[0])               // step 4
	z.C0.Mul(&x.C0, &t[1])            // step 5
	z.C1.Mul(&x.C1, &t[1]).Neg(&z.C1) // step 6

	return z
}

// InverseUnitary inverse a unitary element
// TODO deprecate in favour of Conjugate
func (z *e12) InverseUnitary(x *e12) *e12 {
	return z.Conjugate(x)
}

// Conjugate set z to (x.C0, -x.C1) and return z
func (z *e12) Conjugate(x *e12) *e12 {
	z.Set(x)
	z.C1.Neg(&z.C1)
	return z
}

// MulByVW set z to x*(y*v*w) and return z
// here y*v*w means the e12 element with C1.B1=y and all other components 0
func (z *e12) MulByVW(x *e12, y *e2) *e12 {
	var result e12
	var yNR e2

	{ // begin: inline yNR.MulByNonResidue(y)
		var buf, buf9 e2
		buf.Set(y)
		buf9.Double(&buf).
			Double(&buf9).
			Double(&buf9).
			Add(&buf9, &buf)
		yNR.A1.Add(&buf.A0, &buf9.A1)
		{ // begin: inline MulByNonResidue(&(yNR).A0, &buf.A1)
			(&(yNR).A0).Neg(&buf.A1)
		} // end: inline MulByNonResidue(&(yNR).A0, &buf.A1)
		yNR.A0.AddAssign(&buf9.A0)
	} // end: inline yNR.MulByNonResidue(y)
	result.C0.B0.Mul(&x.C1.B1, &yNR)
	result.C0.B1.Mul(&x.C1.B2, &yNR)
	result.C0.B2.Mul(&x.C1.B0, y)
	result.C1.B0.Mul(&x.C0.B2, &yNR)
	result.C1.B1.Mul(&x.C0.B0, y)
	result.C1.B2.Mul(&x.C0.B1, y)
	z.Set(&result)
	return z
}

// MulByV set z to x*(y*v) and return z
// here y*v means the e12 element with C0.B1=y and all other components 0
func (z *e12) MulByV(x *e12, y *e2) *e12 {
	var result e12
	var yNR e2

	{ // begin: inline yNR.MulByNonResidue(y)
		var buf, buf9 e2
		buf.Set(y)
		buf9.Double(&buf).
			Double(&buf9).
			Double(&buf9).
			Add(&buf9, &buf)
		yNR.A1.Add(&buf.A0, &buf9.A1)
		{ // begin: inline MulByNonResidue(&(yNR).A0, &buf.A1)
			(&(yNR).A0).Neg(&buf.A1)
		} // end: inline MulByNonResidue(&(yNR).A0, &buf.A1)
		yNR.A0.AddAssign(&buf9.A0)
	} // end: inline yNR.MulByNonResidue(y)
	result.C0.B0.Mul(&x.C0.B2, &yNR)
	result.C0.B1.Mul(&x.C0.B0, y)
	result.C0.B2.Mul(&x.C0.B1, y)
	result.C1.B0.Mul(&x.C1.B2, &yNR)
	result.C1.B1.Mul(&x.C1.B0, y)
	result.C1.B2.Mul(&x.C1.B1, y)
	z.Set(&result)
	return z
}

// MulByV2W set z to x*(y*v^2*w) and return z
// here y*v^2*w means the e12 element with C1.B2=y and all other components 0
func (z *e12) MulByV2W(x *e12, y *e2) *e12 {
	var result e12
	var yNR e2

	{ // begin: inline yNR.MulByNonResidue(y)
		var buf, buf9 e2
		buf.Set(y)
		buf9.Double(&buf).
			Double(&buf9).
			Double(&buf9).
			Add(&buf9, &buf)
		yNR.A1.Add(&buf.A0, &buf9.A1)
		{ // begin: inline MulByNonResidue(&(yNR).A0, &buf.A1)
			(&(yNR).A0).Neg(&buf.A1)
		} // end: inline MulByNonResidue(&(yNR).A0, &buf.A1)
		yNR.A0.AddAssign(&buf9.A0)
	} // end: inline yNR.MulByNonResidue(y)
	result.C0.B0.Mul(&x.C1.B0, &yNR)
	result.C0.B1.Mul(&x.C1.B1, &yNR)
	result.C0.B2.Mul(&x.C1.B2, &yNR)
	result.C1.B0.Mul(&x.C0.B1, &yNR)
	result.C1.B1.Mul(&x.C0.B2, &yNR)
	result.C1.B2.Mul(&x.C0.B0, y)
	z.Set(&result)
	return z
}

// MulByV2NRInv set z to x*(y*v^2*(9,1)^{-1}) and return z
// here y*v^2 means the e12 element with C0.B2=y and all other components 0
func (z *e12) MulByV2NRInv(x *e12, y *e2) *e12 {
	var result e12
	var yNRInv e2

	{ // begin: inline yNRInv.MulByNonResidueInv(y)
		// (yNRInv).A0 = (9*(y).A0 + (y).A1)/82
		// (yNRInv).A1 = (9*(y).A1 - (y).A0)/82
		copy := *(y)

		var copy9 e2
		copy9.Double(&copy).
			Double(&copy9).
			Double(&copy9).
			AddAssign(&copy)

		(yNRInv).A0.Add(&copy9.A0, &copy.A1)
		(yNRInv).A1.Sub(&copy9.A1, &copy.A0)

		buf82inv := fp.Element{
			15263610803691847034,
			14617516054323294413,
			1961223913490700324,
			3456812345740674661,
		}
		(yNRInv).A0.MulAssign(&buf82inv)
		(yNRInv).A1.MulAssign(&buf82inv)
	} // end: inline yNRInv.MulByNonResidueInv(y)

	result.C0.B0.Mul(&x.C0.B1, y)
	result.C0.B1.Mul(&x.C0.B2, y)
	result.C0.B2.Mul(&x.C0.B0, &yNRInv)

	result.C1.B0.Mul(&x.C1.B1, y)
	result.C1.B1.Mul(&x.C1.B2, y)
	result.C1.B2.Mul(&x.C1.B0, &yNRInv)

	z.Set(&result)
	return z
}

// MulByVWNRInv set z to x*(y*v*w*(9,1)^{-1}) and return z
// here y*v*w means the e12 element with C1.B1=y and all other components 0
func (z *e12) MulByVWNRInv(x *e12, y *e2) *e12 {
	var result e12
	var yNRInv e2

	{ // begin: inline yNRInv.MulByNonResidueInv(y)
		// (yNRInv).A0 = (9*(y).A0 + (y).A1)/82
		// (yNRInv).A1 = (9*(y).A1 - (y).A0)/82
		copy := *(y)

		var copy9 e2
		copy9.Double(&copy).
			Double(&copy9).
			Double(&copy9).
			AddAssign(&copy)

		(yNRInv).A0.Add(&copy9.A0, &copy.A1)
		(yNRInv).A1.Sub(&copy9.A1, &copy.A0)

		buf82inv := fp.Element{
			15263610803691847034,
			14617516054323294413,
			1961223913490700324,
			3456812345740674661,
		}
		(yNRInv).A0.MulAssign(&buf82inv)
		(yNRInv).A1.MulAssign(&buf82inv)
	} // end: inline yNRInv.MulByNonResidueInv(y)

	result.C0.B0.Mul(&x.C1.B1, y)
	result.C0.B1.Mul(&x.C1.B2, y)
	result.C0.B2.Mul(&x.C1.B0, &yNRInv)

	result.C1.B0.Mul(&x.C0.B2, y)
	result.C1.B1.Mul(&x.C0.B0, &yNRInv)
	result.C1.B2.Mul(&x.C0.B1, &yNRInv)

	z.Set(&result)
	return z
}

// MulByWNRInv set z to x*(y*w*(9,1)^{-1}) and return z
// here y*w means the e12 element with C1.B0=y and all other components 0
func (z *e12) MulByWNRInv(x *e12, y *e2) *e12 {
	var result e12
	var yNRInv e2

	{ // begin: inline yNRInv.MulByNonResidueInv(y)
		// (yNRInv).A0 = (9*(y).A0 + (y).A1)/82
		// (yNRInv).A1 = (9*(y).A1 - (y).A0)/82
		copy := *(y)

		var copy9 e2
		copy9.Double(&copy).
			Double(&copy9).
			Double(&copy9).
			AddAssign(&copy)

		(yNRInv).A0.Add(&copy9.A0, &copy.A1)
		(yNRInv).A1.Sub(&copy9.A1, &copy.A0)

		buf82inv := fp.Element{
			15263610803691847034,
			14617516054323294413,
			1961223913490700324,
			3456812345740674661,
		}
		(yNRInv).A0.MulAssign(&buf82inv)
		(yNRInv).A1.MulAssign(&buf82inv)
	} // end: inline yNRInv.MulByNonResidueInv(y)

	result.C0.B0.Mul(&x.C1.B2, y)
	result.C0.B1.Mul(&x.C1.B0, &yNRInv)
	result.C0.B2.Mul(&x.C1.B1, &yNRInv)

	result.C1.B0.Mul(&x.C0.B0, &yNRInv)
	result.C1.B1.Mul(&x.C0.B1, &yNRInv)
	result.C1.B2.Mul(&x.C0.B2, &yNRInv)

	z.Set(&result)
	return z
}

// MulByNonResidue multiplies a e6 by ((0,0),(1,0),(0,0))
func (z *e6) MulByNonResidue(x *e6) *e6 {
	var result e6
	result.B1.Set(&(x).B0)
	result.B2.Set(&(x).B1)
	{ // begin: inline result.B0.MulByNonResidue(&(x).B2)
		var buf, buf9 e2
		buf.Set(&(x).B2)
		buf9.Double(&buf).
			Double(&buf9).
			Double(&buf9).
			Add(&buf9, &buf)
		result.B0.A1.Add(&buf.A0, &buf9.A1)
		{ // begin: inline MulByNonResidue(&(result.B0).A0, &buf.A1)
			(&(result.B0).A0).Neg(&buf.A1)
		} // end: inline MulByNonResidue(&(result.B0).A0, &buf.A1)
		result.B0.A0.AddAssign(&buf9.A0)
	} // end: inline result.B0.MulByNonResidue(&(x).B2)
	z.Set(&result)
	return z
}

// Frobenius set z to Frobenius(x) in e12 and return z
func (z *e12) Frobenius(x *e12) *e12 {
	// Algorithm 28 from https://eprint.iacr.org/2010/354.pdf (beware typos!)
	var t [6]e2

	// Frobenius acts on fp2 by conjugation
	t[0].Conjugate(&x.C0.B0)
	t[1].Conjugate(&x.C0.B1)
	t[2].Conjugate(&x.C0.B2)
	t[3].Conjugate(&x.C1.B0)
	t[4].Conjugate(&x.C1.B1)
	t[5].Conjugate(&x.C1.B2)

	t[1].MulByNonResiduePower2(&t[1])
	t[2].MulByNonResiduePower4(&t[2])
	t[3].MulByNonResiduePower1(&t[3])
	t[4].MulByNonResiduePower3(&t[4])
	t[5].MulByNonResiduePower5(&t[5])

	z.C0.B0 = t[0]
	z.C0.B1 = t[1]
	z.C0.B2 = t[2]
	z.C1.B0 = t[3]
	z.C1.B1 = t[4]
	z.C1.B2 = t[5]

	return z
}

// FrobeniusSquare set z to Frobenius^2(x) in e12 and return z
func (z *e12) FrobeniusSquare(x *e12) *e12 {
	// Algorithm 29 from https://eprint.iacr.org/2010/354.pdf (beware typos!)
	var t [6]e2

	t[1].MulByNonResiduePowerSquare2(&x.C0.B1)
	t[2].MulByNonResiduePowerSquare4(&x.C0.B2)
	t[3].MulByNonResiduePowerSquare1(&x.C1.B0)
	t[4].MulByNonResiduePowerSquare3(&x.C1.B1)
	t[5].MulByNonResiduePowerSquare5(&x.C1.B2)

	z.C0.B0 = x.C0.B0
	z.C0.B1 = t[1]
	z.C0.B2 = t[2]
	z.C1.B0 = t[3]
	z.C1.B1 = t[4]
	z.C1.B2 = t[5]

	return z
}

// FrobeniusCube set z to Frobenius^3(x) in e12 and return z
func (z *e12) FrobeniusCube(x *e12) *e12 {
	// Algorithm 30 from https://eprint.iacr.org/2010/354.pdf (beware typos!)
	var t [6]e2

	// Frobenius^3 acts on fp2 by conjugation
	t[0].Conjugate(&x.C0.B0)
	t[1].Conjugate(&x.C0.B1)
	t[2].Conjugate(&x.C0.B2)
	t[3].Conjugate(&x.C1.B0)
	t[4].Conjugate(&x.C1.B1)
	t[5].Conjugate(&x.C1.B2)

	t[1].MulByNonResiduePowerCube2(&t[1])
	t[2].MulByNonResiduePowerCube4(&t[2])
	t[3].MulByNonResiduePowerCube1(&t[3])
	t[4].MulByNonResiduePowerCube3(&t[4])
	t[5].MulByNonResiduePowerCube5(&t[5])

	z.C0.B0 = t[0]
	z.C0.B1 = t[1]
	z.C0.B2 = t[2]
	z.C1.B0 = t[3]
	z.C1.B1 = t[4]
	z.C1.B2 = t[5]

	return z
}

// MulByNonResiduePower1 set z=x*(9,1)^(1*(p-1)/6) and return z
func (z *e2) MulByNonResiduePower1(x *e2) *e2 {
	// (9,1)^(1*(p-1)/6)
	// 3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760 + u*151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027
	b := e2{
		A0: fp.Element{
			12653890742059813127,
			14585784200204367754,
			1278438861261381767,
			212598772761311868,
		},
		A1: fp.Element{
			11683091849979440498,
			14992204589386555739,
			15866167890766973222,
			1200023580730561873,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePower2 set z=x*(9,1)^(2*(p-1)/6) and return z
func (z *e2) MulByNonResiduePower2(x *e2) *e2 {
	// (9,1)^(2*(p-1)/6)
	// 0 + u*4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436
	b := e2{
		A0: fp.Element{
			13075984984163199792,
			3782902503040509012,
			8791150885551868305,
			1825854335138010348,
		},
		A1: fp.Element{
			7963664994991228759,
			12257807996192067905,
			13179524609921305146,
			2767831111890561987,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePower3 set z=x*(9,1)^(3*(p-1)/6) and return z
func (z *e2) MulByNonResiduePower3(x *e2) *e2 {
	// (9,1)^(3*(p-1)/6)
	// 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 + u*1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257
	b := e2{
		A0: fp.Element{
			16482010305593259561,
			13488546290961988299,
			3578621962720924518,
			2681173117283399901,
		},
		A1: fp.Element{
			11661927080404088775,
			553939530661941723,
			7860678177968807019,
			3208568454732775116,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePower4 set z=x*(9,1)^(4*(p-1)/6) and return z
func (z *e2) MulByNonResiduePower4(x *e2) *e2 {
	// (9,1)^(4*(p-1)/6)
	// 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437
	b := e2{
		A0: fp.Element{
			8314163329781907090,
			11942187022798819835,
			11282677263046157209,
			1576150870752482284,
		},
		A1: fp.Element{
			6763840483288992073,
			7118829427391486816,
			4016233444936635065,
			2630958277570195709,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePower5 set z=x*(9,1)^(5*(p-1)/6) and return z
func (z *e2) MulByNonResiduePower5(x *e2) *e2 {
	// (9,1)^(5*(p-1)/6)
	// 877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230 + u*3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557
	b := e2{
		A0: fp.Element{
			14515217250696892391,
			16303087968080972555,
			3656613296917993960,
			1345095164996126785,
		},
		A1: fp.Element{
			957117326806663081,
			367382125163301975,
			15253872307375509749,
			3396254757538665050,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePowerSquare1 set z=x*(9,1)^(1*(p^2-1)/6) and return z
func (z *e2) MulByNonResiduePowerSquare1(x *e2) *e2 {
	// (9,1)^(1*(p^2-1)/6)
	// 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351
	b := fp.Element{
		14595462726357228530,
		17349508522658994025,
		1017833795229664280,
		299787779797702374,
	}
	z.A0.Mul(&x.A0, &b)
	z.A1.Mul(&x.A1, &b)
	return z
}

// MulByNonResiduePowerSquare2 set z=x*(9,1)^(2*(p^2-1)/6) and return z
func (z *e2) MulByNonResiduePowerSquare2(x *e2) *e2 {
	// (9,1)^(2*(p^2-1)/6)
	// 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350
	b := fp.Element{
		3697675806616062876,
		9065277094688085689,
		6918009208039626314,
		2775033306905974752,
	}
	z.A0.Mul(&x.A0, &b)
	z.A1.Mul(&x.A1, &b)
	return z
}

// MulByNonResiduePowerSquare3 set z=x*(9,1)^(3*(p^2-1)/6) and return z
func (z *e2) MulByNonResiduePowerSquare3(x *e2) *e2 {
	// (9,1)^(3*(p^2-1)/6)
	// 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786
	b := fp.Element{
		7548957153968385962,
		10162512645738643279,
		5900175412809962033,
		2475245527108272378,
	}
	z.A0.Mul(&x.A0, &b)
	z.A1.Mul(&x.A1, &b)
	return z
}

// MulByNonResiduePowerSquare4 set z=x*(9,1)^(4*(p^2-1)/6) and return z
func (z *e2) MulByNonResiduePowerSquare4(x *e2) *e2 {
	// (9,1)^(4*(p^2-1)/6)
	// 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436
	b := fp.Element{
		8183898218631979349,
		12014359695528440611,
		12263358156045030468,
		3187210487005268291,
	}
	z.A0.Mul(&x.A0, &b)
	z.A1.Mul(&x.A1, &b)
	return z
}

// MulByNonResiduePowerSquare5 set z=x*(9,1)^(5*(p^2-1)/6) and return z
func (z *e2) MulByNonResiduePowerSquare5(x *e2) *e2 {
	// (9,1)^(5*(p^2-1)/6)
	// 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437
	b := fp.Element{
		634941064663593387,
		1851847049789797332,
		6363182743235068435,
		711964959896995913,
	}
	z.A0.Mul(&x.A0, &b)
	z.A1.Mul(&x.A1, &b)
	return z
}

// MulByNonResiduePowerCube1 set z=x*(9,1)^(1*(p^3-1)/6) and return z
func (z *e2) MulByNonResiduePowerCube1(x *e2) *e2 {
	// (9,1)^(1*(p^3-1)/6)
	// 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530 + u*1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257
	b := e2{
		A0: fp.Element{
			3914496794763385213,
			790120733010914719,
			7322192392869644725,
			581366264293887267,
		},
		A1: fp.Element{
			12817045492518885689,
			4440270538777280383,
			11178533038884588256,
			2767537931541304486,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePowerCube2 set z=x*(9,1)^(2*(p^3-1)/6) and return z
func (z *e2) MulByNonResiduePowerCube2(x *e2) *e2 {
	// (9,1)^(2*(p^3-1)/6)
	// 0 + u*1
	b := e2{
		A0: fp.Element{
			14532872967180610477,
			12903226530429559474,
			1868623743233345524,
			2316889217940299650,
		},
		A1: fp.Element{
			12447993766991532972,
			4121872836076202828,
			7630813605053367399,
			740282956577754197,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePowerCube3 set z=x*(9,1)^(3*(p^3-1)/6) and return z
func (z *e2) MulByNonResiduePowerCube3(x *e2) *e2 {
	// (9,1)^(3*(p^3-1)/6)
	// 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530 + u*2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530
	b := e2{
		A0: fp.Element{
			6297350639395948318,
			15875321927225446337,
			9702569988553770230,
			805825149519570764,
		},
		A1: fp.Element{
			11117433864585119104,
			10363184613815941297,
			5420513773305887730,
			278429812070195549,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePowerCube4 set z=x*(9,1)^(4*(p^3-1)/6) and return z
func (z *e2) MulByNonResiduePowerCube4(x *e2) *e2 {
	// (9,1)^(4*(p^3-1)/6)
	// 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786
	b := e2{
		A0: fp.Element{
			4938922280314430175,
			13823286637238282975,
			15589480384090068090,
			481952561930628184,
		},
		A1: fp.Element{
			3105754162722846417,
			11647802298615474591,
			13057042392041828081,
			1660844386505564338,
		},
	}
	z.Mul(x, &b)
	return z
}

// MulByNonResiduePowerCube5 set z=x*(9,1)^(5*(p^3-1)/6) and return z
func (z *e2) MulByNonResiduePowerCube5(x *e2) *e2 {
	// (9,1)^(5*(p^3-1)/6)
	// 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 + u*2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530
	b := e2{
		A0: fp.Element{
			16193900971494954399,
			13995139551301264911,
			9239559758168096094,
			1571199014989505406,
		},
		A1: fp.Element{
			3254114329011132839,
			11171599147282597747,
			10965492220518093659,
			2657556514797346915,
		},
	}
	z.Mul(x, &b)
	return z
}

const tAbsVal uint64 = 4965661367192848881

// Expt set z to x^t in e12 and return z
// TODO make a ExptAssign method that assigns the result to self; then this method can assert fail if z != x
// TODO Expt is the only method that depends on tAbsVal.  The rest of the tower does not depend on this value.  Logically, Expt should be separated from the rest of the tower.
func (z *e12) Expt(x *e12) *e12 {
	// TODO what if x==0?
	// TODO make this match Element.Exp: x is a non-pointer?
	var result e12
	result.Set(x)

	l := bits.Len64(tAbsVal) - 2
	for i := l; i >= 0; i-- {
		result.Square(&result)
		if tAbsVal&(1<<uint(i)) != 0 {
			result.Mul(&result, x)
		}
	}

	z.Set(&result)
	return z
}

// FinalExponentiation computes the final expo x**((p**12 - 1)/r)
func (z *e12) FinalExponentiation(x *e12) *e12 {
	// For BN curves use Section 5 of https://eprint.iacr.org/2008/490.pdf; their x is our t

	// TODO modify sage test points script to include a factor of 3 in the final exponent for BLS curves but not BN curves
	var mt [4]e12 // mt[i] is m^(t^i)

	// set m[0] = x^((p^6-1)*(p^2+1))
	{
		mt[0].Set(x)
		var temp e12
		temp.FrobeniusCube(&mt[0]).
			FrobeniusCube(&temp)

		mt[0].Inverse(&mt[0])
		temp.Mul(&temp, &mt[0])

		mt[0].FrobeniusSquare(&temp).
			Mul(&mt[0], &temp)
	}

	// "hard part": set z = m[0]^((p^4-p^2+1)/r)

	mt[1].Expt(&mt[0])
	mt[2].Expt(&mt[1])
	mt[3].Expt(&mt[2])

	// prepare y
	var y [7]e12

	y[1].InverseUnitary(&mt[0])
	y[4].Set(&mt[1])
	y[5].InverseUnitary(&mt[2])
	y[6].Set(&mt[3])

	mt[0].Frobenius(&mt[0])
	mt[1].Frobenius(&mt[1])
	mt[2].Frobenius(&mt[2])
	mt[3].Frobenius(&mt[3])

	y[0].Set(&mt[0])
	y[3].InverseUnitary(&mt[1])
	y[4].Mul(&y[4], &mt[2]).InverseUnitary(&y[4])
	y[6].Mul(&y[6], &mt[3]).InverseUnitary(&y[6])

	mt[0].Frobenius(&mt[0])
	mt[2].Frobenius(&mt[2])

	y[0].Mul(&y[0], &mt[0])
	y[2].Set(&mt[2])

	mt[0].Frobenius(&mt[0])

	y[0].Mul(&y[0], &mt[0])

	// compute addition chain
	var t [2]e12

	t[0].Square(&y[6])
	t[0].Mul(&t[0], &y[4])
	t[0].Mul(&t[0], &y[5])
	t[1].Mul(&y[3], &y[5])
	t[1].Mul(&t[1], &t[0])
	t[0].Mul(&t[0], &y[2])
	t[1].Square(&t[1])
	t[1].Mul(&t[1], &t[0])
	t[1].Square(&t[1])
	t[0].Mul(&t[1], &y[1])
	t[1].Mul(&t[1], &y[0])
	t[0].Square(&t[0])
	z.Mul(&t[0], &t[1])

	return z
}
