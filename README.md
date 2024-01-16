# Pallier Encryption Chip for Halo2

This Rust library includes ready-to-use chip for performing Pallier Partial Homomorphic Encryption inside a Halo2 circuit.

## Theory

### Encryption
The Paillier encryption system encrypts a message `m` with a public key `(n, g)` to produce a ciphertext `c`, using the equation: 

    c = g^m . r^n mod n^2
where: 
- `m` is the plaintext message. 
- `n`  is a large prime number, part of the public key, and \( n^2 \) is the ciphertext 

space.
- `g` is the generator in Z<sub>*</sub><sup>n^2</sup>
-  `r` is a random number in Z<sub>*</sub><sup>n</sup>

### Addition
Given two ciphertexts `c_1`  and `c_2`, which are the encryption of plaintexts `m_1` and `m_2` under the same public key `(n, g)`, the homomorphic addition is performed as follows:

    c_sum = c_1 . c_2 mod n^2

## Setup & Installation

1. **Clone the repository:**
```bash
git clone https://github.com/aerius-labs/pallier-encryption-halo2.git
```
2. **Navigate to the project directory:**
```bash
cd pallier-encryption-halo2
```
3. **Building the project:**
```bash
cargo build --release
```
## Running Tests
```bash
cargo run test
```  
## Contributing
We welcome contributions from the community!

## License
This project is UNLICENSED.