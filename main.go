package main

import (
	"bytes"
	"crypto/rand"
	"crypto/sha256"
	"errors"
	"fmt"
	"log"
	"math/big"

	"github.com/cloudflare/bn256" 
)

// Constants for security parameters
const (
	SecurityParameter = 256
	BlockSize         = 32
)

// Transaction represents an encrypted transaction
type Transaction struct {
	C1 *bn256.G2 // First component of ciphertext
	C2 []byte    // Second component of ciphertext
	C3 [][]byte  // Third component (encrypted blocks)
}

// Keyper represents a network validator
type Keyper struct {
	ID       int
	MskShare *big.Int  // Share of master secret key
	MPK      *bn256.G2 // Master public key
}

// System parameters
type Params struct {
	MPK   *bn256.G2 // Master public key
	G1Gen *bn256.G1 // Generator of G1
	G2Gen *bn256.G2 // Generator of G2
}

func H1(eon int64) *bn256.G1 {
	h := sha256.New()
	h.Write(big.NewInt(eon).Bytes())

	reader := bytes.NewReader(h.Sum(nil))

	_, point, _ := bn256.RandomG1(reader)
	// this is deterministic todo: figure out how to do it in sp1
	return point
}


func H2(gt *bn256.GT) []byte {
	h := sha256.New()
	h.Write(gt.Marshal())
	return h.Sum(nil)
}


func H3(sigma []byte, msg []byte) *big.Int {
	h := sha256.New()
	h.Write(sigma)
	h.Write(msg)

	bytes := h.Sum(nil)
	r := new(big.Int).SetBytes(bytes)
	return r.Mod(r, bn256.Order)
}

func H4(sigma []byte, counter int) []byte {
	h := sha256.New()
	h.Write(sigma)
	h.Write(big.NewInt(int64(counter)).Bytes())
	return h.Sum(nil)
}

func Setup(n, t int) ([]*Keyper, *Params, error) {
	// Generate master secret key
	msk, _ := rand.Int(rand.Reader, bn256.Order)

	// Generate master public key
	g2 := new(bn256.G2).ScalarBaseMult(big.NewInt(1))
	// msk exists in G2
	mpk := new(bn256.G2).ScalarMult(g2, msk)

	// Generate polynomial coefficients for secret sharing
	coeffs := make([]*big.Int, t)
	coeffs[0] = msk
	for i := 1; i < t; i++ {
		coeffs[i], _ = rand.Int(rand.Reader, bn256.Order)
	}

	// Generate shares for keypers
	keypers := make([]*Keyper, n)
	for i := 0; i < n; i++ {
		x := big.NewInt(int64(i + 1))
		share := evaluatePolynomial(coeffs, x)

		keypers[i] = &Keyper{
			ID:       i + 1,
			MskShare: share,
			MPK:      mpk,
		}
	}

	params := &Params{
		MPK:   mpk,
		G1Gen: new(bn256.G1).ScalarBaseMult(big.NewInt(1)),
		G2Gen: g2,
	}

	return keypers, params, nil
}

// Post encrypts a transaction for a given eon
func Post(params *Params, msg []byte, eon int64) (*Transaction, error) {
	// Generate random sigma
	sigma := make([]byte, SecurityParameter/8)
	if _, err := rand.Read(sigma); err != nil {
		return nil, err
	}

	// Compute r = H3(sigma, msg)
	r := H3(sigma, msg)

	// Compute C1 = r*P2
	c1 := new(bn256.G2).ScalarMult(params.G2Gen, r)

	// Compute e(H1(i), mpk)^r
	h1i := H1(eon)
	gt := bn256.Pair(h1i, params.MPK)
	gt = gt.ScalarMult(gt, r)

	// Compute C2 = sigma xor H2(gt)
	h2gt := H2(gt)
	c2 := make([]byte, len(sigma))
	for i := range sigma {
		c2[i] = sigma[i] ^ h2gt[i]
	}

	// Split message into blocks and encrypt
	numBlocks := (len(msg) + BlockSize - 1) / BlockSize
	c3 := make([][]byte, numBlocks)

	for i := 0; i < numBlocks; i++ {
		start := i * BlockSize
		end := start + BlockSize
		if end > len(msg) {
			end = len(msg)
		}

		block := msg[start:end]
		pad := make([]byte, BlockSize-len(block))
		block = append(block, pad...)

		keyStream := H4(sigma, i+1)
		c3[i] = make([]byte, BlockSize)
		for j := range block {
			c3[i][j] = block[j] ^ keyStream[j]
		}
	}

	return &Transaction{
		C1: c1,
		C2: c2,
		C3: c3,
	}, nil
}

// ComputeShare computes a keyper's share for an eon
func (k *Keyper) ComputeShare(eon int64) *bn256.G1 {
	h1i := H1(eon)
	return new(bn256.G1).ScalarMult(h1i, k.MskShare)
}

// CombineShares combines t+1 shares to recover the eon secret key
func CombineShares(shares map[int]*bn256.G1) *bn256.G1 {
	result := new(bn256.G1).ScalarBaseMult(big.NewInt(0))
	order := bn256.Order // Add this line to define order

	points := make([]int, 0, len(shares))
	for id := range shares {
		points = append(points, id)
	}

	for j, xj := range points {
		lambda := big.NewInt(1)
		for m, xm := range points {
			if m == j {
				continue
			}

			num := big.NewInt(int64(xm))
			den := big.NewInt(int64(xm - xj))
			den = den.Mod(den, order)
			if den.Sign() < 0 {
				den.Add(den, order)
			}

			denInv := new(big.Int).ModInverse(den, order)
			if denInv == nil {
				continue 
			}

			num = num.Mul(num, denInv)
			num = num.Mod(num, order)
			lambda = lambda.Mul(lambda, num)
			lambda = lambda.Mod(lambda, order)
		}

		// Multiply share by lambda and add to result
		contrib := new(bn256.G1).ScalarMult(shares[xj], lambda)
		result.Add(result, contrib)
	}

	return result
}

// Decrypt decrypts a transaction using the eon secret key
func Decrypt(sk *bn256.G1, tx *Transaction) ([]byte, error) {
	// Compute e(sk, C1)
	gt := bn256.Pair(sk, tx.C1)

	// Recover sigma
	h2gt := H2(gt)
	sigma := make([]byte, len(tx.C2))
	for i := range tx.C2 {
		sigma[i] = tx.C2[i] ^ h2gt[i]
	}

	// For Decrypted message blocks
	msg := make([]byte, 0, len(tx.C3)*BlockSize)

	for i, block := range tx.C3 {
		keyStream := H4(sigma, i+1)
		plaintext := make([]byte, len(block))
		for j := range block {
			plaintext[j] = block[j] ^ keyStream[j]
		}

		// Remove padding from last block
		if i == len(tx.C3)-1 {
			// Find where padding starts
			for j := len(plaintext) - 1; j >= 0; j-- {
				if plaintext[j] != 0 {
					plaintext = plaintext[:j+1]
					break
				}
			}
		}

		msg = append(msg, plaintext...)
	}

	// Verify r
	r := H3(sigma, msg)
	c1Check := new(bn256.G2).ScalarBaseMult(r)

	if !bytes.Equal(c1Check.Marshal(), tx.C1.Marshal()) {
		return nil, errors.New("decryption verification failed")
	}

	return msg, nil
}

// Helper function to evaluate polynomial
func evaluatePolynomial(coeffs []*big.Int, x *big.Int) *big.Int {
	result := new(big.Int).Set(coeffs[0])
	tmp := new(big.Int)
	xPow := new(big.Int).Set(x)

	for i := 1; i < len(coeffs); i++ {
		tmp.Mul(coeffs[i], xPow)
		result.Add(result, tmp)
		xPow.Mul(xPow, x)
	}

	return result.Mod(result, bn256.Order)
}

func main() {
	// Test configuration
	numKeypers := 500
	threshold := 251
	eon := int64(1)
	testMessage := []byte("Hello, Shutter Network! This is a test message.")

	fmt.Println("=== Shutter Network Test ===")
	fmt.Printf("Number of Keypers: %d\n", numKeypers)
	fmt.Printf("Threshold: %d\n", threshold)
	fmt.Printf("Test Message: %s\n", string(testMessage))
	fmt.Println("============================")

	// Generate keypers and system parameters
	fmt.Println("\n1. Setting up system parameters and keypers...")
	keypers, params, err := Setup(numKeypers, threshold)
	if err != nil {
		log.Fatalf("Setup failed: %v", err)
	}
	fmt.Printf("Successfully generated %d keypers\n", len(keypers))

	// Print MPK
	mpkBytes := params.MPK.Marshal()
	fmt.Printf("Master Public Key: %x\n", mpkBytes[:])

	// Encrypt message
	fmt.Println("\n2. Encrypting message for eon", eon)
	tx, err := Post(params, testMessage, eon)
	if err != nil {
		log.Fatalf("Encryption failed: %v", err)
	}

	// Print ciphertext components
	c1Bytes := tx.C1.Marshal()
	fmt.Printf("C1 : %x\n", c1Bytes[:])
	fmt.Printf("C2 : %x\n", tx.C2[:])
	fmt.Printf("Number of C3 blocks: %d\n", len(tx.C3))

	// Generate shares for eon
	fmt.Println("\n3. Generating keyper shares for eon", eon)
	shares := make(map[int]*bn256.G1)
	for _, keyper := range keypers {
		share := keyper.ComputeShare(eon)
		shares[keyper.ID] = share

		// Print first few bytes of each share
		shareBytes := share.Marshal()
		fmt.Printf("Keyper %d share : %x\n",
			keyper.ID,
			shareBytes[:])
	}

	// Combine shares
	fmt.Println("\n4. Combining shares to get eon secret key...")
	sk := CombineShares(shares)
	skBytes := sk.Marshal()
	fmt.Printf("Eon secret key: %x\n", skBytes[:])

	// Decrypt message
	fmt.Println("\n5. Decrypting message...")
	decrypted, err := Decrypt(sk, tx)
	if err != nil {
		log.Fatalf("Decryption failed: %v", err)
	}

	// Verify result
	fmt.Println("\n=== Test Results ===")
	fmt.Printf("Original message: %s\n", string(testMessage))
	fmt.Printf("Decrypted message: %s\n", string(decrypted))

	if string(decrypted) == string(testMessage) {
		fmt.Println("\nSUCCESS: Messages match!")
	} else {
		fmt.Println("\nFAILURE: Messages don't match!")
		fmt.Printf("Original length: %d, Decrypted length: %d\n",
			len(testMessage),
			len(decrypted))
	}

	// Test with fewer shares than threshold
	fmt.Println("\n6. Testing threshold security...")
	insufficientShares := make(map[int]*bn256.G1)
	for i := 0; i < threshold-1; i++ {
		insufficientShares[keypers[i].ID] = shares[keypers[i].ID]
	}

	fmt.Printf("Attempting decryption with %d shares (threshold is %d)...\n",
		len(insufficientShares),
		threshold)

	skInsufficient := CombineShares(insufficientShares)
	_, err = Decrypt(skInsufficient, tx)
	if err != nil {
		fmt.Println("SUCCESS: Decryption failed with insufficient shares as expected")
	} else {
		fmt.Println("FAILURE: Decryption succeeded with insufficient shares!")
	}

	// Test message manipulation
	fmt.Println("\n7. Testing message manipulation resistance...")
	modifiedTx := *tx
	modifiedTx.C2[0] ^= 1 // Flip one bit

	_, err = Decrypt(sk, &modifiedTx)
	if err != nil {
		fmt.Println("SUCCESS: Modified message failed to decrypt as expected")
	} else {
		fmt.Println("FAILURE: Modified message decrypted successfully!")
	}

	fmt.Println("\n=== Test Complete ===")
}
