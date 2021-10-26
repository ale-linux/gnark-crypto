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

package bn254

import (
	"errors"

	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark-crypto/ecc/bn254/internal/fptower"
)

// GT target group of the pairing
type GT = fptower.E12

type lineEvaluation struct {
	r0 fptower.E2
	r1 fptower.E2
	r2 fptower.E2
}

// Pair calculates the reduced pairing for a set of points
func Pair(P []G1Affine, Q []G2Affine) (GT, error) {
	f, err := MillerLoop(P, Q)
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

	// https://eprint.iacr.org/2008/490.pdf
	var mt [4]GT // mt[i] is m^(t^i)

	// easy part
	mt[0].Set(&result)
	var temp GT
	temp.Conjugate(&mt[0])
	mt[0].Inverse(&mt[0])
	temp.Mul(&temp, &mt[0])
	mt[0].FrobeniusSquare(&temp).
		Mul(&mt[0], &temp)

	// hard part
	mt[1].Expt(&mt[0])
	mt[2].Expt(&mt[1])
	mt[3].Expt(&mt[2])

	var y [7]GT

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
	mt[0].CyclotomicSquare(&y[6])
	mt[0].Mul(&mt[0], &y[4])
	mt[0].Mul(&mt[0], &y[5])
	mt[1].Mul(&y[3], &y[5])
	mt[1].Mul(&mt[1], &mt[0])
	mt[0].Mul(&mt[0], &y[2])
	mt[1].CyclotomicSquare(&mt[1])
	mt[1].Mul(&mt[1], &mt[0])
	mt[1].CyclotomicSquare(&mt[1])
	mt[0].Mul(&mt[1], &y[1])
	mt[1].Mul(&mt[1], &y[0])
	mt[0].CyclotomicSquare(&mt[0])
	result.Mul(&mt[0], &mt[1])

	return result
}

// MillerLoop Miller loop
func MillerLoop(P []G1Affine, Q []G2Affine) (GT, error) {
	// f, err := MillerLoopOptAte(P, Q)
	// f, err := MillerLoopTate(P, Q)
	// f, err := MillerLoopOptTate(P, Q)
	f, err := MillerLoopOptTateParallel(P, Q)

	return f, err
}

// MillerLoopOptAte optimal ate Miller loop
func MillerLoopOptAte(P []G1Affine, Q []G2Affine) (GT, error) {
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
	qNeg := make([]G2Affine, n)
	for k := 0; k < n; k++ {
		qProj[k].FromAffine(&q[k])
		qNeg[k].Neg(&q[k])
	}

	var result GT
	result.SetOne()

	var l lineEvaluation

	for i := len(loopCounterOptAte) - 2; i >= 0; i-- {
		result.Square(&result)

		for k := 0; k < n; k++ {
			qProj[k].DoubleStep(&l)
			// line evaluation
			l.r0.MulByElement(&l.r0, &p[k].Y)
			l.r1.MulByElement(&l.r1, &p[k].X)
			result.MulBy034(&l.r0, &l.r1, &l.r2)

			if loopCounterOptAte[i] == 1 {
				qProj[k].AddMixedStep(&l, &q[k])
				// line evaluation
				l.r0.MulByElement(&l.r0, &p[k].Y)
				l.r1.MulByElement(&l.r1, &p[k].X)
				result.MulBy034(&l.r0, &l.r1, &l.r2)

			} else if loopCounterOptAte[i] == -1 {
				qProj[k].AddMixedStep(&l, &qNeg[k])
				// line evaluation
				l.r0.MulByElement(&l.r0, &p[k].Y)
				l.r1.MulByElement(&l.r1, &p[k].X)
				result.MulBy034(&l.r0, &l.r1, &l.r2)
			}
		}
	}

	var Q1, Q2 G2Affine
	var l0 lineEvaluation
	var tmp GT
	// cf https://eprint.iacr.org/2010/354.pdf for instance for optimal Ate Pairing
	for k := 0; k < n; k++ {
		//Q1 = Frob(Q)
		Q1.X.Conjugate(&q[k].X).MulByNonResidue1Power2(&Q1.X)
		Q1.Y.Conjugate(&q[k].Y).MulByNonResidue1Power3(&Q1.Y)

		// Q2 = -Frob2(Q)
		Q2.X.MulByNonResidue2Power2(&q[k].X)
		Q2.Y.MulByNonResidue2Power3(&q[k].Y).Neg(&Q2.Y)

		qProj[k].AddMixedStep(&l0, &Q1)
		l0.r0.MulByElement(&l0.r0, &p[k].Y)
		l0.r1.MulByElement(&l0.r1, &p[k].X)

		qProj[k].AddMixedStep(&l, &Q2)
		l.r0.MulByElement(&l.r0, &p[k].Y)
		l.r1.MulByElement(&l.r1, &p[k].X)
		tmp.Mul034By034(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
		result.Mul(&result, &tmp)
	}

	return result, nil
}

// MillerLoopTate Tate Miller loop
func MillerLoopTate(P []G1Affine, Q []G2Affine) (GT, error) {
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
	pProj := make([]g1Proj, n)
	pNeg := make([]G1Affine, n)
	for k := 0; k < n; k++ {
		pProj[k].FromAffine(&p[k])
		pNeg[k].Neg(&p[k])
	}

	var result GT
	result.SetOne()

	var l lineEvaluation

	// i == 253
	for k := 0; k < n; k++ {
		pProj[k].DoubleStep(&l)
		// line evaluation
		l.r2.Mul(&l.r2, &q[k].Y)
		l.r1.Mul(&l.r1, &q[k].X)
		result.MulBy014(&l.r0, &l.r1, &l.r2)
	}

	for i := 252; i >= 0; i-- {
		result.Square(&result)

		for k := 0; k < n; k++ {
			pProj[k].DoubleStep(&l)
			// line evaluation
			l.r2.Mul(&l.r2, &q[k].Y)
			l.r1.Mul(&l.r1, &q[k].X)
			result.MulBy014(&l.r0, &l.r1, &l.r2)

			if loopCounterTate[i] == 1 {
				pProj[k].AddMixedStep(&l, &p[k])
				// line evaluation
				l.r2.Mul(&l.r2, &q[k].Y)
				l.r1.Mul(&l.r1, &q[k].X)
				result.MulBy014(&l.r0, &l.r1, &l.r2)

			} else if loopCounterTate[i] == -1 {
				pProj[k].AddMixedStep(&l, &pNeg[k])
				// line evaluation
				l.r2.Mul(&l.r2, &q[k].Y)
				l.r1.Mul(&l.r1, &q[k].X)
				result.MulBy014(&l.r0, &l.r1, &l.r2)
			}
		}
	}

	return result, nil
}

// MillerLoopOptTate optimal Tate Miller loop
func MillerLoopOptTate(P []G1Affine, Q []G2Affine) (GT, error) {
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
	pProj := make([]g1Proj, n)
	pProjPsi := make([]g1Proj, n)
	pNeg := make([]G1Affine, n)
	pPsi := make([]G1Affine, n)
	pPsiNeg := make([]G1Affine, n)
	for k := 0; k < n; k++ {
		pProj[k].FromAffine(&p[k])
		pNeg[k].Neg(&p[k])
		pPsiNeg[k].X.Mul(&p[k].X, &thirdRootOneG1)
		pPsiNeg[k].Y.Set(&p[k].Y)
		pPsi[k].Neg(&pPsiNeg[k])
		pProjPsi[k].FromAffine(&pPsi[k])
	}

	var result1, result2 GT
	result1.SetOne()

	var l lineEvaluation

	for i := len(loopCounterOptTate0) - 2; i >= 0; i-- {
		result1.Square(&result1)

		for k := 0; k < n; k++ {
			pProj[k].DoubleStep(&l)
			// line evaluation
			l.r2.Mul(&l.r2, &q[k].Y)
			l.r1.Mul(&l.r1, &q[k].X)
			result1.MulBy014(&l.r0, &l.r1, &l.r2)

			if loopCounterOptTate0[i] == 1 {
				pProj[k].AddMixedStep(&l, &p[k])
				// line evaluation
				l.r2.Mul(&l.r2, &q[k].Y)
				l.r1.Mul(&l.r1, &q[k].X)
				result1.MulBy014(&l.r0, &l.r1, &l.r2)

			} else if loopCounterOptTate0[i] == -1 {
				pProj[k].AddMixedStep(&l, &pNeg[k])
				// line evaluation
				l.r2.Mul(&l.r2, &q[k].Y)
				l.r1.Mul(&l.r1, &q[k].X)
				result1.MulBy014(&l.r0, &l.r1, &l.r2)
			}
		}
	}

	result2.SetOne()

	for i := len(loopCounterOptTate1) - 2; i >= 0; i-- {
		result2.Square(&result2)

		for k := 0; k < n; k++ {
			pProjPsi[k].DoubleStep(&l)
			// line evaluation
			l.r2.Mul(&l.r2, &q[k].Y)
			l.r1.Mul(&l.r1, &q[k].X)
			result2.MulBy014(&l.r0, &l.r1, &l.r2)

			if loopCounterOptTate1[i] == 1 {
				pProjPsi[k].AddMixedStep(&l, &pPsi[k])
				// line evaluation
				l.r2.Mul(&l.r2, &q[k].Y)
				l.r1.Mul(&l.r1, &q[k].X)
				result2.MulBy014(&l.r0, &l.r1, &l.r2)

			} else if loopCounterOptTate1[i] == -1 {
				pProjPsi[k].AddMixedStep(&l, &pPsiNeg[k])
				// line evaluation
				l.r2.Mul(&l.r2, &q[k].Y)
				l.r1.Mul(&l.r1, &q[k].X)
				result2.MulBy014(&l.r0, &l.r1, &l.r2)
			}
		}
	}

	result2.Mul(&result2, &result1)

	return result2, nil
}

// MillerLoopOptTateParallel optimal Tate Miller loop
func MillerLoopOptTateParallel(P []G1Affine, Q []G2Affine) (GT, error) {
	// check input size match
	n := len(P)
	if n == 0 || n != len(Q) {
		return GT{}, errors.New("invalid inputs sizes")
	}

	// filter infinity points
	p0 := make([]G1Affine, 0, n)
	q := make([]G2Affine, 0, n)

	for k := 0; k < n; k++ {
		if P[k].IsInfinity() || Q[k].IsInfinity() {
			continue
		}
		p0 = append(p0, P[k])
		q = append(q, Q[k])
	}

	n = len(q)

	// precomputations
	pProj1 := make([]g1Proj, n)
	p1 := make([]G1Affine, n)
	p01 := make([]G1Affine, n)
	p10 := make([]G1Affine, n)
	pProj01 := make([]g1Proj, n) // P0+P1
	pProj10 := make([]g1Proj, n) // P0-P1
	l01 := make([]lineEvaluation, n)
	l10 := make([]lineEvaluation, n)
	for k := 0; k < n; k++ {
		p1[k].Y.Neg(&p0[k].Y)
		p1[k].X.Mul(&p0[k].X, &thirdRootOneG1)
		pProj1[k].FromAffine(&p1[k])

		// l_{p0,p1}(q)
		pProj01[k].Set(&pProj1[k])
		pProj01[k].AddMixedStep(&l01[k], &p0[k])
		l01[k].r1.Mul(&l01[k].r1, &q[k].X)
		l01[k].r2.Mul(&l01[k].r2, &q[k].Y)

		// l_{p0,-p1}(q)
		pProj10[k].Neg(&pProj1[k])
		pProj10[k].AddMixedStep(&l10[k], &p0[k])
		l10[k].r1.Mul(&l10[k].r1, &q[k].X)
		l10[k].r2.Mul(&l10[k].r2, &q[k].Y)
	}
	BatchProjectiveToAffineG1(pProj01, p01)
	BatchProjectiveToAffineG1(pProj10, p10)

	// f_{a0+lambda*a1,P}(Q)
	var result, ss GT
	result.SetOne()
	var l, l0 lineEvaluation

	var j int8

	// i = 126
	for k := 0; k < n; k++ {
		pProj1[k].DoubleStep(&l0)
		l0.r1.Mul(&l0.r1, &q[k].X)
		l0.r2.Mul(&l0.r2, &q[k].Y)
		result.MulBy014(&l0.r0, &l0.r1, &l0.r2)
	}

	var tmp G1Affine
	for i := 125; i >= 0; i-- {
		result.Square(&result)

		j = loopCounterOptTate1[i]*3 + loopCounterOptTate00[i]

		for k := 0; k < n; k++ {
			pProj1[k].DoubleStep(&l0)
			l0.r1.Mul(&l0.r1, &q[k].X)
			l0.r2.Mul(&l0.r2, &q[k].Y)

			switch j {
			case -4:
				tmp.Neg(&p01[k])
				pProj1[k].AddMixedStep(&l, &tmp)
				l.r1.Mul(&l.r1, &q[k].X)
				l.r2.Mul(&l.r2, &q[k].Y)
				ss.Mul014By014(&l.r0, &l.r1, &l.r2, &l01[k].r0, &l01[k].r1, &l01[k].r2)
				result.MulBy014(&l0.r0, &l0.r1, &l0.r2).
					Mul(&result, &ss)
			case -3:
				tmp.Neg(&p1[k])
				pProj1[k].AddMixedStep(&l, &tmp)
				l.r1.Mul(&l.r1, &q[k].X)
				l.r2.Mul(&l.r2, &q[k].Y)
				ss.Mul014By014(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
				result.Mul(&result, &ss)
			case -2:
				pProj1[k].AddMixedStep(&l, &p10[k])
				l.r1.Mul(&l.r1, &q[k].X)
				l.r2.Mul(&l.r2, &q[k].Y)
				ss.Mul014By014(&l.r0, &l.r1, &l.r2, &l10[k].r0, &l10[k].r1, &l10[k].r2)
				result.MulBy014(&l0.r0, &l0.r1, &l0.r2).
					Mul(&result, &ss)
			case -1:
				tmp.Neg(&p0[k])
				pProj1[k].AddMixedStep(&l, &tmp)
				l.r1.Mul(&l.r1, &q[k].X)
				l.r2.Mul(&l.r2, &q[k].Y)
				ss.Mul014By014(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
				result.Mul(&result, &ss)
			case 0:
				result.MulBy014(&l0.r0, &l0.r1, &l0.r2)
			case 1:
				pProj1[k].AddMixedStep(&l, &p0[k])
				l.r1.Mul(&l.r1, &q[k].X)
				l.r2.Mul(&l.r2, &q[k].Y)
				ss.Mul014By014(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
				result.Mul(&result, &ss)
			case 2:
				tmp.Neg(&p10[k])
				pProj1[k].AddMixedStep(&l, &tmp)
				l.r1.Mul(&l.r1, &q[k].X)
				l.r2.Mul(&l.r2, &q[k].Y)
				ss.Mul014By014(&l.r0, &l.r1, &l.r2, &l10[k].r0, &l10[k].r1, &l10[k].r2)
				result.MulBy014(&l0.r0, &l0.r1, &l0.r2).
					Mul(&result, &ss)
			case 3:
				pProj1[k].AddMixedStep(&l, &p1[k])
				l.r1.Mul(&l.r1, &q[k].X)
				l.r2.Mul(&l.r2, &q[k].Y)
				ss.Mul014By014(&l.r0, &l.r1, &l.r2, &l0.r0, &l0.r1, &l0.r2)
				result.Mul(&result, &ss)
			case 4:
				pProj1[k].AddMixedStep(&l, &p01[k])
				l.r1.Mul(&l.r1, &q[k].X)
				l.r2.Mul(&l.r2, &q[k].Y)
				ss.Mul014By014(&l.r0, &l.r1, &l.r2, &l01[k].r0, &l01[k].r1, &l01[k].r2)
				result.MulBy014(&l0.r0, &l0.r1, &l0.r2).
					Mul(&result, &ss)
			default:
				return GT{}, errors.New("invalid loopCounter")
			}
		}
	}

	return result, nil
}

// DoubleStep doubles a point in Homogenous projective coordinates, and evaluates the line in Miller loop
// https://eprint.iacr.org/2013/722.pdf (Section 4.3)
func (p *g2Proj) DoubleStep(evaluations *lineEvaluation) {

	// get some Element from our pool
	var t1, A, B, C, D, E, EE, F, G, H, I, J, K fptower.E2
	A.Mul(&p.x, &p.y)
	A.Halve()
	B.Square(&p.y)
	C.Square(&p.z)
	D.Double(&C).
		Add(&D, &C)
	E.Mul(&D, &bTwistCurveCoeff)
	F.Double(&E).
		Add(&F, &E)
	G.Add(&B, &F)
	G.Halve()
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

// For Tate pairing
// DoubleStep doubles a point in Homogenous projective coordinates, and evaluates the line in Miller loop
// https://eprint.iacr.org/2013/722.pdf (Section 4.3)
func (p *g1Proj) DoubleStep(l *lineEvaluation) {

	// get some Element from our pool
	var t1, A, B, C, D, E, EE, F, G, H, I, J, K fp.Element
	A.Mul(&p.x, &p.y)
	A.Halve()
	B.Square(&p.y)
	C.Square(&p.z)
	D.Double(&C).
		Add(&D, &C)
	E.Mul(&D, &bCurveCoeff)
	F.Double(&E).
		Add(&F, &E)
	G.Add(&B, &F)
	G.Halve()
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
	l.r0.A0.Set(&I)
	l.r0.A1.SetZero()
	l.r1.A0.Double(&J).
		Add(&l.r1.A0, &J)
	l.r1.A1.SetZero()
	l.r2.A0.Neg(&H)
	l.r2.A1.SetZero()

}

// AddMixedStep point addition in Mixed Homogenous projective and Affine coordinates
// https://eprint.iacr.org/2013/722.pdf (Section 4.3)
func (p *g1Proj) AddMixedStep(l *lineEvaluation, a *G1Affine) {

	// get some Element from our pool
	var Y2Z1, X2Z1, O, L, C, D, E, F, G, H, t0, t1, t2, J fp.Element
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
	l.r0.A0.Set(&J)
	l.r0.A1.SetZero()
	l.r1.A0.Neg(&O)
	l.r1.A1.SetZero()
	l.r2.A0.Set(&L)
	l.r2.A1.SetZero()
}
