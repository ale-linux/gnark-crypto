//go:build gofuzz
// +build gofuzz

// Copyright 2020 ConsenSys Software Inc.
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

// Code generated by consensys/gnark-crypto DO NOT EDIT

package fft

import (
	"bytes"
	"fmt"
	"github.com/consensys/gnark-crypto/ecc"

	"github.com/consensys/gnark-crypto/ecc/bw6-633/fr"
)

const (
	fuzzInteresting = 1
	fuzzNormal      = 0
	fuzzDiscard     = -1
)

func Fuzz(data []byte) int {
	r := bytes.NewReader(data)

	// random polynomial
	size := len(data) / 8
	if size == 0 {
		return fuzzDiscard
	}
	if size > (1 << 15) {
		size = 1 << 15
	}
	paddedSize := ecc.NextPowerOfTwo(uint64(size))
	p1 := make([]fr.Element, paddedSize)
	p2 := make([]fr.Element, paddedSize)
	for i := 0; i < len(p1); i++ {
		p1[i].SetRawBytes(r)
	}
	copy(p2, p1)

	// fft domain
	nbCosets := uint64(uint8(data[0]) % 3)
	domainWithPrecompute := NewDomain(paddedSize, nbCosets, true)
	domainWOPrecompute := NewDomain(paddedSize, nbCosets, false)

	// bitReverse(DIF FFT(DIT FFT (bitReverse))))==id
	for i := uint64(0); i < nbCosets; i++ {
		BitReverse(p1)
		domainWithPrecompute.FFT(p1, DIT, i)
		domainWOPrecompute.FFTInverse(p1, DIF, i)
		BitReverse(p1)

		for i := 0; i < len(p1); i++ {
			if !p1[i].Equal(&p2[i]) {
				panic(fmt.Sprintf("bitReverse(DIF FFT(DIT FFT (bitReverse)))) != id, size %d", size))
			}
		}
	}

	return fuzzNormal
}
