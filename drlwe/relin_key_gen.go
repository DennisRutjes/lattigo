package drlwe

import (
	"errors"
	"math"

	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/utils"
)

// RelinearizationKeyGenerator is an interface describing the local steps of a generic RLWE RKG protocol
type RelinearizationKeyGenerator interface {
	AllocateShares() (ephKey ring.Poly, r1 *RKGShare, r2 *RKGShare)
	GenShareRoundOne(sk *ring.Poly, crp []*ring.Poly, ephKeyOut *ring.Poly, shareOut *RKGShare)
	GenShareRoundTwo(u, sk *ring.Poly, round1Share *RKGShare, crp []*ring.Poly, shareOut *RKGShare)
	AggregateShares(share1, share2, shareOut *RKGShare)
	GenRelinearizationKey(round1 *RKGShare, round2 *RKGShare, evalKeyOut [][2]*ring.Poly)
}

// RKGProtocol is the structure storing the parameters and and precomputations for the collective relinearization key generation protocol.
type RKGProtocol struct {
	ringQModCount   uint64
	alpha           uint64
	beta            uint64
	ringP           *ring.Ring
	ringQP          *ring.Ring
	gaussianSampler *ring.GaussianSampler
	ternarySampler  *ring.TernarySampler // sampling in Montgomerry form

	tmpPoly1 *ring.Poly
	tmpPoly2 *ring.Poly
}

// RKGShare is a share in the RKG protocol
type RKGShare struct {
	value [][2]*ring.Poly
}

// NewRKGProtocol creates a new RKG protocol struct
func NewRKGProtocol(n uint64, q, p []uint64, ephSkPr, sigma float64) *RKGProtocol {
	rkg := new(RKGProtocol)
	rkg.ringQModCount = uint64(len(q))
	rkg.alpha = uint64(len(p))
	if rkg.alpha != 0 {
		rkg.beta = uint64(math.Ceil(float64(len(q)) / float64(len(p))))
	} else {
		rkg.beta = 1
	}
	var err error
	rkg.ringP, err = ring.NewRing(n, p)
	if err != nil {
		panic(err) // TODO error
	}
	rkg.ringQP, err = ring.NewRing(n, append(q, p...))
	if err != nil {
		panic(err) // TODO error
	}
	prng, err := utils.NewPRNG()
	if err != nil {
		panic(err) // TODO error
	}
	rkg.gaussianSampler = ring.NewGaussianSampler(prng, rkg.ringQP, sigma, uint64(6*sigma))
	rkg.ternarySampler = ring.NewTernarySampler(prng, rkg.ringQP, ephSkPr, true)
	rkg.tmpPoly1, rkg.tmpPoly2 = rkg.ringQP.NewPoly(), rkg.ringQP.NewPoly()
	return rkg
}

// AllocateShares allocates the shares of the EKG protocol.
func (ekg *RKGProtocol) AllocateShares() (ephSk *ring.Poly, r1 *RKGShare, r2 *RKGShare) {
	ephSk = ekg.ringQP.NewPoly()
	r1, r2 = new(RKGShare), new(RKGShare)
	r1.value = make([][2]*ring.Poly, ekg.beta)
	r2.value = make([][2]*ring.Poly, ekg.beta)
	for i := uint64(0); i < ekg.beta; i++ {
		r1.value[i][0] = ekg.ringQP.NewPoly()
		r1.value[i][1] = ekg.ringQP.NewPoly()
		r2.value[i][0] = ekg.ringQP.NewPoly()
		r2.value[i][1] = ekg.ringQP.NewPoly()
	}
	return
}

// GenShareRoundOne is the first of three rounds of the RKGProtocol protocol. Each party generates a pseudo encryption of
// its secret share of the key s_i under its ephemeral key u_i : [-u_i*a + s_i*w + e_i] and broadcasts it to the other
// j-1 parties.
func (ekg *RKGProtocol) GenShareRoundOne(sk *ring.Poly, crp []*ring.Poly, ephSkOut *ring.Poly, shareOut *RKGShare) {
	// Given a base decomposition w_i (here the CRT decomposition)
	// computes [-u*a_i + P*s_i + e_i]
	// where a_i = crp_i

	ekg.ternarySampler.Read(ephSkOut)
	ekg.ringQP.NTT(ephSkOut, ephSkOut)

	ekg.tmpPoly1.Copy(sk)
	ekg.ringQP.MulScalarBigint(ekg.tmpPoly1, ekg.ringP.ModulusBigint, ekg.tmpPoly1)
	ekg.ringQP.InvMForm(ekg.tmpPoly1, ekg.tmpPoly1)

	for i := uint64(0); i < ekg.beta; i++ {
		// h = e
		ekg.gaussianSampler.Read(shareOut.value[i][0])
		ekg.ringQP.NTT(shareOut.value[i][0], shareOut.value[i][0])

		// h = sk*CrtBaseDecompQi + e
		for j := uint64(0); j < ekg.alpha; j++ {
			index := i*ekg.alpha + j
			qi := ekg.ringQP.Modulus[index]
			skP := ekg.tmpPoly1.Coeffs[index]
			h := shareOut.value[i][0].Coeffs[index]

			for w := uint64(0); w < ekg.ringQP.N; w++ {
				h[w] = ring.CRed(h[w]+skP[w], qi)
			}

			// Handles the case where nb pj does not divides nb qi
			if index == uint64(ekg.ringQModCount) {
				break
			}
		}

		// h = sk*CrtBaseDecompQi + -u*a + e
		ekg.ringQP.MulCoeffsMontgomeryAndSub(ephSkOut, crp[i], shareOut.value[i][0])

		// Second Element
		// e_2i
		ekg.gaussianSampler.Read(shareOut.value[i][1])
		ekg.ringQP.NTT(shareOut.value[i][1], shareOut.value[i][1])
		// s*a + e_2i
		ekg.ringQP.MulCoeffsMontgomeryAndAdd(sk, crp[i], shareOut.value[i][1])
	}

	//ekg.tmpPoly1.Zero()
}

// GenShareRoundTwo is the second of three rounds of the RKGProtocol protocol. Upon receiving the j-1 shares, each party computes :
//
// [s_i * sum([-u_j*a + s_j*w + e_j]) + e_i1, s_i*a + e_i2]
//
// = [s_i * (-u*a + s*w + e) + e_i1, s_i*a + e_i2]
//
// and broadcasts both values to the other j-1 parties.
func (ekg *RKGProtocol) GenShareRoundTwo(round1 *RKGShare, ephSk, sk *ring.Poly, crp []*ring.Poly, shareOut *RKGShare) {
	// (u_i - s_i)
	ekg.ringQP.Sub(ephSk, sk, ekg.tmpPoly1)

	// Each sample is of the form [-u*a_i + s*w_i + e_i]
	// So for each element of the base decomposition w_i :
	for i := uint64(0); i < ekg.beta; i++ {

		// Computes [(sum samples)*sk + e_1i, sk*a + e_2i]

		// (AggregateShareRoundTwo samples) * sk
		ekg.ringQP.MulCoeffsMontgomery(round1.value[i][0], sk, shareOut.value[i][0])

		// (AggregateShareRoundTwo samples) * sk + e_1i
		ekg.gaussianSampler.Read(ekg.tmpPoly2)
		ekg.ringQP.NTT(ekg.tmpPoly2, ekg.tmpPoly2)
		ekg.ringQP.Add(shareOut.value[i][0], ekg.tmpPoly2, shareOut.value[i][0])

		// second part
		// (u - s) * (sum [x][s*a_i + e_2i]) + e3i
		ekg.gaussianSampler.Read(shareOut.value[i][1])
		ekg.ringQP.NTT(shareOut.value[i][1], shareOut.value[i][1])
		ekg.ringQP.MulCoeffsMontgomeryAndAdd(ekg.tmpPoly1, round1.value[i][1], shareOut.value[i][1])
	}

}

// AggregateShares combines two RKG shares into a single one
func (ekg *RKGProtocol) AggregateShares(share1, share2, shareOut *RKGShare) {

	for i := uint64(0); i < ekg.beta; i++ {
		ekg.ringQP.Add(share1.value[i][0], share2.value[i][0], shareOut.value[i][0])
		ekg.ringQP.Add(share1.value[i][1], share2.value[i][1], shareOut.value[i][1])
	}
}

func (ekg *RKGProtocol) GenRelinearizationKey(round1 *RKGShare, round2 *RKGShare, evalKeyOut [][2]*ring.Poly) {
	for i := uint64(0); i < ekg.beta; i++ {
		ekg.ringQP.Add(round2.value[i][0], round2.value[i][1], evalKeyOut[i][0])
		evalKeyOut[i][1].Copy(round1.value[i][1])

		ekg.ringQP.MForm(evalKeyOut[i][0], evalKeyOut[i][0])
		ekg.ringQP.MForm(evalKeyOut[i][1], evalKeyOut[i][1])
	}
}

// MarshalBinary encodes the target element on a slice of bytes.
func (share *RKGShare) MarshalBinary() ([]byte, error) {
	//we have modulus * bitLog * Len of 1 ring rings
	rLength := (share.value[0])[0].GetDataLen(true)
	data := make([]byte, 1+2*rLength*uint64(len(share.value)))
	if len(share.value) > 0xFF {
		return []byte{}, errors.New("RKGShare : uint8 overflow on length")
	}
	data[0] = uint8(len(share.value))

	//write all of our rings in the data.
	//write all the polys
	ptr := uint64(1)
	for _, elem := range share.value {
		_, err := elem[0].WriteTo(data[ptr : ptr+rLength])
		if err != nil {
			return []byte{}, err
		}
		ptr += rLength
		_, err = elem[1].WriteTo(data[ptr : ptr+rLength])
		if err != nil {
			return []byte{}, err
		}
		ptr += rLength
	}

	return data, nil

}

// UnmarshalBinary decodes a slice of bytes on the target element.
func (share *RKGShare) UnmarshalBinary(data []byte) error {
	lenShare := data[0]
	rLength := (len(data) - 1) / (2 * int(lenShare))

	if share.value == nil {
		share.value = make([][2]*ring.Poly, lenShare)
	}
	ptr := (1)
	for i := (0); i < int(lenShare); i++ {
		if share.value[i][0] == nil || share.value[i][1] == nil {
			share.value[i][0] = new(ring.Poly)
			share.value[i][1] = new(ring.Poly)
		}

		err := share.value[i][0].UnmarshalBinary(data[ptr : ptr+rLength])
		if err != nil {
			return err
		}
		ptr += rLength
		err = share.value[i][1].UnmarshalBinary(data[ptr : ptr+rLength])
		if err != nil {
			return err
		}
		ptr += rLength

	}

	return nil
}
