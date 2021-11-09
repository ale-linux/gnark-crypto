package fp

import (
	"math/bits"
)

func max(a int, b int) int {
	if a > b {
		return a
	}
	return b
}

func min(a int, b int) int {
	if a < b {
		return a
	}
	return b
}

func approximate(x *Element, n int) uint64 {

	if n <= 64 {
		return x[0]
	}

	mask := uint64(0x7FFFFFFF) //31 ones
	lo := mask & x[0]

	hiWordIndex := (n - 1) / 64

	hiWordBitsAvailable := n - hiWordIndex*64
	hiWordBitsUsed := min(hiWordBitsAvailable, 33)

	mask = ^((1 << (hiWordBitsAvailable - hiWordBitsUsed)) - 1)
	hi := (x[hiWordIndex] & mask) << (64 - hiWordBitsAvailable)

	mask = ^(1<<(31+hiWordBitsUsed) - 1)
	mid := (mask & x[hiWordIndex-1]) >> hiWordBitsUsed

	return lo | mid | hi
}

func approximatePair(x *Element, y *Element) (uint64, uint64) {
	n := max(x.BitLen(), y.BitLen())

	return approximate(x, n), approximate(y, n)
}

var inversionCorrectionFactorP20Full = Element{5743661648749932980, 12551916556084744593, 23273105902916091, 802172129993363311}

func (z *Element) Inverse(x *Element) *Element {
	if x.IsZero() {
		z.SetZero()
		return z
	}

	var a = *x
	var b = qElement
	var u = Element{1, 0, 0, 0}
	var v = Element{0, 0, 0, 0}

	// registers are 64bit, thus k = 32
	const outerLoopIterations = 16 // ceil( (2* 254 - 1)/32 )

	//Update factors: we get [u; v]:= [f0 g0; f1 g1] [u; v]
	var f0, g0, f1, g1 int64

	//Saved update factors to reduce the number of field multiplications
	var pf0, pg0, pf1, pg1 int64

	for i := 0; i < outerLoopIterations; i++ {
		aApprox, bApprox := approximatePair(&a, &b)
		f0, g0, f1, g1 = 1, 0, 0, 1

		for j := 0; j < 31; j++ {

			if aApprox&1 == 0 {
				aApprox /= 2
			} else {
				if aApprox < bApprox {
					aApprox, bApprox = bApprox, aApprox
					f0, f1 = f1, f0
					g0, g1 = g1, g0
				}

				aApprox = (aApprox - bApprox) / 2
				f0 -= f1
				g0 -= g1

			}

			f1 *= 2
			g1 *= 2

		}

		scratch := a
		aHi := a.bigNumLinearComb(&scratch, f0, &b, g0)
		bHi := b.bigNumLinearComb(&scratch, f1, &b, g1)

		if aHi&0x8000000000000000 != 0 {
			f0, g0 = -f0, -g0
			aHi = a.bigNumNeg(&a, aHi)
		}
		if bHi&0x8000000000000000 != 0 {
			f1, g1 = -f1, -g1
			bHi = b.bigNumNeg(&b, bHi)
		}

		a.bigNumRshBy31(&a, aHi)
		b.bigNumRshBy31(&b, bHi)

		if i%2 == 1 || i == outerLoopIterations-1 { //second condition is redundant in this case

			f0, g0, f1, g1 = f0*pf0+g0*pf1,
				f0*pg0+g0*pg1,
				f1*pf0+g1*pf1,
				f1*pg0+g1*pg1

			var updateFactor Element
			//save u
			scratch.Set(&u)

			//update u
			u.MulWord(&u, f0)

			updateFactor.MulWord(&v, g0)
			u.Add(&u, &updateFactor)

			//update v
			scratch.MulWord(&scratch, f1)

			v.MulWord(&v, g1)
			v.Add(&v, &scratch)

		} else {
			pf0, pg0, pf1, pg1 = f0, g0, f1, g1
		}

	}

	z.Mul(&v, &inversionCorrectionFactorP20Full)
	return z
}

//TODO: Do this directly
//TODO: If not done directly, the absolute value of y is less than half of uint64's capacity, could mean more carries are certainly zero
func (z *Element) MulWord(x *Element, y int64) {
	var neg bool
	var abs uint64

	if y < 0 {
		neg = true
		abs = uint64(-y)
	} else {
		neg = false
		abs = uint64(y)
	}

	z.mulWordUnsigned(x, abs)

	if neg {
		z.Neg(z)
	}
}

//Would making this package private encourage Go to inline it?
func (z *Element) mulWordUnsigned(x *Element, y uint64) {

	var t [4]uint64
	var c [3]uint64
	{
		// round 0
		v := x[0]
		c[1], c[0] = bits.Mul64(v, y)
		m := c[0] * 9786893198990664585
		c[2] = madd0(m, 4332616871279656263, c[0])

		c[2], t[0] = madd2(m, 10917124144477883021, c[2], c[1])
		c[2], t[1] = madd2(m, 13281191951274694749, c[2], 0)
		t[3], t[2] = madd1(m, 3486998266802970665, c[2])

	}
	{
		// round 1
		v := x[1]
		c[1], c[0] = madd1(v, y, t[0])
		m := c[0] * 9786893198990664585
		c[2] = madd0(m, 4332616871279656263, c[0])

		c[0], c[1] = bits.Add64(c[1], t[1], 0)
		c[2], t[0] = madd2(m, 10917124144477883021, c[2], c[0])

		c[0], c[1] = bits.Add64(c[1], t[2], 0)
		c[2], t[1] = madd2(m, 13281191951274694749, c[2], c[0])

		c[0], c[1] = bits.Add64(c[1], t[3], 0)
		t[3], t[2] = madd3(m, 3486998266802970665, c[0], c[2], c[1])
	}
	{
		// round 2
		v := x[2]
		c[1], c[0] = madd1(v, y, t[0])
		m := c[0] * 9786893198990664585
		c[2] = madd0(m, 4332616871279656263, c[0])

		c[0], c[1] = bits.Add64(c[1], t[1], 0)
		c[2], t[0] = madd2(m, 10917124144477883021, c[2], c[0])

		c[0], c[1] = bits.Add64(c[1], t[2], 0)
		c[2], t[1] = madd2(m, 13281191951274694749, c[2], c[0])

		c[0], c[1] = bits.Add64(c[1], t[3], 0)
		t[3], t[2] = madd3(m, 3486998266802970665, c[0], c[2], c[1])
	}
	{
		// round 3
		v := x[3]
		c[1], c[0] = madd1(v, y, t[0])
		m := c[0] * 9786893198990664585
		c[2] = madd0(m, 4332616871279656263, c[0])

		c[0], c[1] = bits.Add64(c[1], t[1], 0)
		c[2], z[0] = madd2(m, 10917124144477883021, c[2], c[0])

		c[0], c[1] = bits.Add64(c[1], t[2], 0)
		c[2], z[1] = madd2(m, 13281191951274694749, c[2], c[0])

		c[0], c[1] = bits.Add64(c[1], t[3], 0)
		z[3], z[2] = madd3(m, 3486998266802970665, c[0], c[2], c[1])
	}

	// if z > q --> z -= q
	// note: this is NOT constant time
	if !(z[3] < 3486998266802970665 || (z[3] == 3486998266802970665 && (z[2] < 13281191951274694749 || (z[2] == 13281191951274694749 && (z[1] < 10917124144477883021 || (z[1] == 10917124144477883021 && (z[0] < 4332616871279656263))))))) {
		var b uint64
		z[0], b = bits.Sub64(z[0], 4332616871279656263, 0)
		z[1], b = bits.Sub64(z[1], 10917124144477883021, b)
		z[2], b = bits.Sub64(z[2], 13281191951274694749, b)
		z[3], _ = bits.Sub64(z[3], 3486998266802970665, b)
	}
}

func (z *Element) bigNumMultiply(x *Element, y int64) uint64 {
	var carry uint64

	var hi uint64
	var hi2 uint64 //these two variables alternate as holding the high word of the current multiplication and that of the previous one

	neg := y < 0
	var abs uint64

	if neg {
		abs = uint64(-y)
	} else {
		abs = uint64(y)
	}

	hi, z[0] = bits.Mul64(x[0], abs) //doesn't matter if z = x. We'll never again have to use the value x[0]

	hi2, z[1] = bits.Mul64(x[1], abs)
	z[1], carry = bits.Add64(z[1], hi, 0)

	hi, z[2] = bits.Mul64(x[2], abs)
	z[2], carry = bits.Add64(z[2], hi2, carry)

	hi2, z[3] = bits.Mul64(x[3], abs)
	z[3], carry = bits.Add64(z[3], hi, carry)

	carry = hi2 + carry //can we do this when not caring about carry?

	if neg {
		carry = z.bigNumNeg(z, carry)
	}

	return carry
}

func (z *Element) bigNumNeg(x *Element, xHi uint64) uint64 {

	z[0], z[1], z[2], z[3], xHi = ^x[0], ^x[1], ^x[2], ^x[3], ^xHi
	var carry uint64
	z[0], carry = bits.Add64(z[0], 1, 0)
	z[1], carry = bits.Add64(z[1], 0, carry)
	z[2], carry = bits.Add64(z[2], 0, carry)
	z[3], carry = bits.Add64(z[3], 0, carry)
	xHi, _ = bits.Add64(xHi, 0, carry)

	return xHi
}

func (z *Element) bigNumAdd(x *Element, xHi uint64, y *Element, yHi uint64) uint64 {
	var carry uint64
	z[0], carry = bits.Add64(x[0], y[0], 0)
	z[1], carry = bits.Add64(x[1], y[1], carry)
	z[2], carry = bits.Add64(x[2], y[2], carry)
	z[3], carry = bits.Add64(x[3], y[3], carry)
	carry, _ = bits.Add64(xHi, yHi, carry)

	return carry
}

func (z *Element) bigNumRshBy31(x *Element, xHi uint64) {
	mask := uint64(0x7FFFFFFF) //31 ones
	z[0] = (x[0] >> 31) | ((x[1] & mask) << 33)
	z[1] = (x[1] >> 31) | ((x[2] & mask) << 33)
	z[2] = (x[2] >> 31) | ((x[3] & mask) << 33)
	z[3] = (x[3] >> 31) | ((xHi & mask) << 33)
}

func (z *Element) bigNumLinearComb(x *Element, xCoeff int64, y *Element, yCoeff int64) uint64 {
	var xTimes Element
	var yTimes Element

	xHi := xTimes.bigNumMultiply(x, xCoeff)
	yHi := yTimes.bigNumMultiply(y, yCoeff)
	hi := z.bigNumAdd(&xTimes, xHi, &yTimes, yHi)

	return hi
}
