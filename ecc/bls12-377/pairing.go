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

package bls12377

import (
	"errors"

	"github.com/consensys/gnark-crypto/ecc/bls12-377/internal/fptower"
)

// GT target group of the pairing
type GT = fptower.E12

type lineEvaluation struct {
	r0 fptower.E2
	r1 fptower.E2
	r2 fptower.E2
}

// mlStep the i-th ml step contains (f,q) where q=[i]Q, f=f_{i,Q}(P) where (f_{i,Q})=i(Q)-([i]Q)-(i-1)O
type mlStep struct {
	f GT
	q []g2Proj
}

// evalLine evaluates the line through q, r at p, where q is on the twist
func evalLine(l *lineEvaluation, q, r *g2Proj) {

	var t fptower.E2

	// compute line equation r0*x+r1*y+r2
	t.Mul(&q.z, &r.y)
	l.r0.Mul(&q.y, &r.z).Sub(&l.r0, &t)
	t.Mul(&q.x, &r.z)
	l.r1.Mul(&q.z, &r.x).Sub(&l.r1, &t)
	t.Mul(&q.y, &r.x)
	l.r2.Mul(&q.x, &r.y).Sub(&l.r2, &t)

}

// Pair calculates the reduced pairing for a set of points
func Pair(P []G1Affine, Q []G2Affine) (GT, error) {
	//f, err := MillerLoop(P, Q)
	f, err := MillerLoopSA(P, Q)
	if err != nil {
		return GT{}, err
	}
	return FinalExponentiation(&f), nil
}

// PairingCheck calculates the reduced pairing for a set of points and returns True if the result is One
func PairingCheck(P []G1Affine, Q []G2Affine) (bool, error) {
	f, err := Pair(P, Q)
	if err != nil {
		return false, err
	}
	var one GT
	one.SetOne()
	return f.Equal(&one), nil
}

// FinalExponentiation computes the final expo x**(p**6-1)(p**2+1)(p**4 - p**2 +1)/r
func FinalExponentiation(z *GT, _z ...*GT) GT {

	var result GT
	result.Set(z)

	for _, e := range _z {
		result.Mul(&result, e)
	}

	// https://eprint.iacr.org/2016/130.pdf
	var t [3]GT

	// easy part
	t[0].Conjugate(&result)
	result.Inverse(&result)
	t[0].Mul(&t[0], &result)
	result.FrobeniusSquare(&t[0]).
		Mul(&result, &t[0])

	// hard part (up to permutation)
	// Daiki Hayashida and Kenichiro Hayasaka
	// and Tadanori Teruya
	// https://eprint.iacr.org/2020/875.pdf
	t[0].CyclotomicSquare(&result)
	t[1].Expt(&result)
	t[2].InverseUnitary(&result)
	t[1].Mul(&t[1], &t[2])
	t[2].Expt(&t[1])
	t[1].InverseUnitary(&t[1])
	t[1].Mul(&t[1], &t[2])
	t[2].Expt(&t[1])
	t[1].Frobenius(&t[1])
	t[1].Mul(&t[1], &t[2])
	result.Mul(&result, &t[0])
	t[0].Expt(&t[1])
	t[2].Expt(&t[0])
	t[0].FrobeniusSquare(&t[1])
	t[1].InverseUnitary(&t[1])
	t[1].Mul(&t[1], &t[2])
	t[1].Mul(&t[1], &t[0])
	result.Mul(&result, &t[1])

	return result
}

// MillerLoop Miller loop
func MillerLoopSA(P []G1Affine, Q []G2Affine) (GT, error) {

	// check input size match
	n := len(P)
	if n == 0 || n != len(Q) {
		return GT{}, errors.New("invalid inputs sizes")
	}

	// filter infinity points
	p := make([]G1Affine, 0, n)
	q := make([]G2Affine, 0, n)

	for k := 0; k < n; k++ {
		if P[k].IsInfinity() || Q[k].IsInfinity() {
			continue
		}
		p = append(p, P[k])
		q = append(q, Q[k])
	}

	n = len(p)

	// projective points for Q
	qProj := make([]g2Proj, n)
	for k := 0; k < n; k++ {
		qProj[k].FromAffine(&q[k])
	}

	var result GT
	result.SetOne()

	var l lineEvaluation

	fsquareStep := func() {
		for k := 0; k < n; k++ {
			qProj[k].DoubleStep(&l)
			l.r0.MulByElement(&l.r0, &p[k].Y)
			l.r1.MulByElement(&l.r1, &p[k].X)
			result.MulBy034(&l.r0, &l.r1, &l.r2)
		}
	}

	squareStep := func() {
		result.Square(&result)
		for k := 0; k < n; k++ {
			qProj[k].DoubleStep(&l)
			l.r0.MulByElement(&l.r0, &p[k].Y)
			l.r1.MulByElement(&l.r1, &p[k].X)
			result.MulBy034(&l.r0, &l.r1, &l.r2)
		}
	}

	mulStep := func() {
		for k := 0; k < n; k++ {
			qProj[k].AddMixedStep(&l, &q[k])
			l.r0.MulByElement(&l.r0, &p[k].Y)
			l.r1.MulByElement(&l.r1, &p[k].X)
			result.MulBy034(&l.r0, &l.r1, &l.r2)
		}
	}

	nSquare := func(n int) {
		for i := 0; i < n; i++ {
			squareStep()
		}
	}

	var ml33 mlStep
	ml33.q = make([]g2Proj, n)
	fsquareStep()
	nSquare(4)
	mulStep()
	ml33.f.Set(&result)
	copy(ml33.q, qProj)
	nSquare(7)
	result.Mul(&result, &ml33.f)

	for k := 0; k < n; k++ {
		evalLine(&l, &ml33.q[k], &qProj[k])
		l.r0.MulByElement(&l.r0, &p[k].X)
		l.r1.MulByElement(&l.r1, &p[k].Y)
		result.MulBy235(&l.r1, &l.r0, &l.r2)
		qProj[k].Add(&ml33.q[k], &qProj[k])
	}

	nSquare(4)
	mulStep()
	squareStep()
	mulStep()

	// remaining 46 bits
	nSquare(46)
	mulStep()

	return result, nil
}

// MillerLoop Miller loop
func MillerLoop(P []G1Affine, Q []G2Affine) (GT, error) {
	// check input size match
	n := len(P)
	if n == 0 || n != len(Q) {
		return GT{}, errors.New("invalid inputs sizes")
	}

	// filter infinity points
	p := make([]G1Affine, 0, n)
	q := make([]G2Affine, 0, n)

	for k := 0; k < n; k++ {
		if P[k].IsInfinity() || Q[k].IsInfinity() {
			continue
		}
		p = append(p, P[k])
		q = append(q, Q[k])
	}

	n = len(p)

	// projective points for Q
	qProj := make([]g2Proj, n)
	for k := 0; k < n; k++ {
		qProj[k].FromAffine(&q[k])
	}

	var result GT
	result.SetOne()

	var l lineEvaluation

	// i == 62
	for k := 0; k < n; k++ {
		qProj[k].DoubleStep(&l)
		// line eval
		l.r0.MulByElement(&l.r0, &p[k].Y)
		l.r1.MulByElement(&l.r1, &p[k].X)
		result.MulBy034(&l.r0, &l.r1, &l.r2)
	}

	for i := 61; i >= 0; i-- {
		result.Square(&result)

		for k := 0; k < n; k++ {
			qProj[k].DoubleStep(&l)
			// line eval
			l.r0.MulByElement(&l.r0, &p[k].Y)
			l.r1.MulByElement(&l.r1, &p[k].X)
			result.MulBy034(&l.r0, &l.r1, &l.r2)
		}

		if loopCounter[i] == 0 {
			continue
		}

		for k := 0; k < n; k++ {
			qProj[k].AddMixedStep(&l, &q[k])
			// line eval
			l.r0.MulByElement(&l.r0, &p[k].Y)
			l.r1.MulByElement(&l.r1, &p[k].X)
			result.MulBy034(&l.r0, &l.r1, &l.r2)
		}
	}

	return result, nil
}

// DoubleStep doubles a point in Homogenous projective coordinates, and evaluates the line in Miller loop
// https://eprint.iacr.org/2013/722.pdf (Section 4.3)
func (p *g2Proj) DoubleStep(evaluations *lineEvaluation) {

	// get some Element from our pool
	var t0, t1, A, B, C, D, E, EE, F, G, H, I, J, K fptower.E2
	t0.Mul(&p.x, &p.y)
	A.MulByElement(&t0, &twoInv)
	B.Square(&p.y)
	C.Square(&p.z)
	D.Double(&C).
		Add(&D, &C)
	E.Mul(&D, &bTwistCurveCoeff)
	F.Double(&E).
		Add(&F, &E)
	G.Add(&B, &F)
	G.MulByElement(&G, &twoInv)
	H.Add(&p.y, &p.z).
		Square(&H)
	t1.Add(&B, &C)
	H.Sub(&H, &t1)
	I.Sub(&E, &B)
	J.Square(&p.x)
	EE.Square(&E)
	K.Double(&EE).
		Add(&K, &EE)

	// X, Y, Z
	p.x.Sub(&B, &F).
		Mul(&p.x, &A)
	p.y.Square(&G).
		Sub(&p.y, &K)
	p.z.Mul(&B, &H)

	// Line evaluation
	evaluations.r0.Neg(&H)
	evaluations.r1.Double(&J).
		Add(&evaluations.r1, &J)
	evaluations.r2.Set(&I)
}

// Add adds 2 points in projective coordinates
func (p *g2Proj) Add(p1, p2 *g2Proj) *g2Proj {

	var y1z2, x1z2, z1z2, u, uu, v, vv, vvv, R, A E2
	y1z2.Mul(&p1.y, &p2.z)
	x1z2.Mul(&p1.x, &p2.z)
	z1z2.Mul(&p1.z, &p2.z)
	u.Mul(&p2.y, &p1.z).Sub(&u, &y1z2)
	uu.Square(&u)
	v.Mul(&p2.x, &p1.z).Sub(&v, &x1z2)
	vv.Square(&v)
	vvv.Mul(&vv, &v)
	R.Mul(&vv, &x1z2)
	A.Mul(&uu, &z1z2).Sub(&A, &vvv).Sub(&A, &R).Sub(&A, &R)
	p.x.Mul(&v, &A)
	p.y.Sub(&R, &A).Mul(&p.y, &u)
	uu.Mul(&vvv, &y1z2)
	p.y.Sub(&p.y, &uu)
	p.z.Mul(&vvv, &z1z2)
	return p

}

// AddMixedStep point addition in Mixed Homogenous projective and Affine coordinates
// https://eprint.iacr.org/2013/722.pdf (Section 4.3)
func (p *g2Proj) AddMixedStep(evaluations *lineEvaluation, a *G2Affine) {

	// get some Element from our pool
	var Y2Z1, X2Z1, O, L, C, D, E, F, G, H, t0, t1, t2, J fptower.E2
	Y2Z1.Mul(&a.Y, &p.z)
	O.Sub(&p.y, &Y2Z1)
	X2Z1.Mul(&a.X, &p.z)
	L.Sub(&p.x, &X2Z1)
	C.Square(&O)
	D.Square(&L)
	E.Mul(&L, &D)
	F.Mul(&p.z, &C)
	G.Mul(&p.x, &D)
	t0.Double(&G)
	H.Add(&E, &F).
		Sub(&H, &t0)
	t1.Mul(&p.y, &E)

	// X, Y, Z
	p.x.Mul(&L, &H)
	p.y.Sub(&G, &H).
		Mul(&p.y, &O).
		Sub(&p.y, &t1)
	p.z.Mul(&E, &p.z)

	t2.Mul(&L, &a.Y)
	J.Mul(&a.X, &O).
		Sub(&J, &t2)

	// Line evaluation
	evaluations.r0.Set(&L)
	evaluations.r1.Neg(&O)
	evaluations.r2.Set(&J)
}
