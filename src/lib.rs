mod aes;

use aes::{AES_DECRYPT, AES_ENCRYPT};

pub type Block = [u8; 16];

fn xor_block(dest: &mut [u8], a: &Block, b: &Block) {
    for i in 0..16 {
        dest[i] = a[i] ^ b[i];
    }
}

fn copy_block(dest: &mut [u8], src: &[u8]) {
    dest[..16].copy_from_slice(&src[..16]);
}

fn shl_block(res: &mut Block, a: &Block) {
    for i in 0..15 {
        res[i] = (a[i] << 1) | (a[i + 1] >> 7);
    }
    res[15] = a[15] << 1;
}

fn gf128_mul2(res: &mut Block, a: &Block) {
    let msb = a[0] & 0x80;
    shl_block(res, a);
    if msb > 0 {
        res[15] ^= 0x87;
    }
}

fn gf128_mul3(res: &mut Block, a: &Block) {
    let mut b = [0u8; 16];
    gf128_mul2(&mut b, a);
    xor_block(res, &b, a)
}

fn gf128_mul7(res: &mut Block, a: &Block) {
    let mut b = [0u8; 16];
    let mut c = [0u8; 16];
    gf128_mul2(&mut b, a);
    gf128_mul2(&mut c, &b);
    let c2 = c;
    xor_block(&mut c, &c2, &b);
    xor_block(res, &c, a);
}

fn rho(block: &mut Block, w: &mut Block) {
    let mut new_w = [0u8; 16];
    gf128_mul2(&mut new_w, w);
    let new_w2 = new_w;
    xor_block(&mut new_w, &new_w2, block);
    xor_block(block, &new_w, w);
    copy_block(w, &new_w)
}

fn rho_inv(block: &mut Block, w: &mut Block) {
    let mut new_w = [0u8; 16];
    gf128_mul2(&mut new_w, w);
    let w2 = *w;
    xor_block(w, &w2, block);
    xor_block(block, &new_w, w)
}

fn mac(out: &mut [u8], _in: &[u8], nonce: &[u8; 8], LL: &Block, key: &Block) {
    let (mut v, mut delta, mut block) = ([0u8; 16], [0u8; 16], [0u8; 16]);
    let mut i = 0;
    let mut len = _in.len();
    let mut previous = 0;
    let mut current = 16;

    gf128_mul3(&mut delta, LL);
    v[..8].copy_from_slice(&nonce[..]);
    let v2 = v;
    xor_block(&mut v, &v2, &delta);

    AES_ENCRYPT(&mut v, key);

    while len >= 16 {
        let delta2 = delta;
        gf128_mul2(&mut delta, &delta2);
        xor_block(
            &mut block,
            _in[previous..current].try_into().expect("LOL"),
            &delta,
        );
        AES_ENCRYPT(&mut block, key);

        let v2 = v;
        xor_block(&mut v, &v2, &block);

        previous += 16;
        current += 16;
        len -= 16;
    }

    if len > 0 {
        gf128_mul7(&mut block, &delta);
        while i < len {
            block[i] ^= _in[i];
            i += 1;
        }
        block[len] ^= 0x80;
        AES_ENCRYPT(&mut block, key);
        xor_block(out, &v, &block);
    } else {
        copy_block(out, &v);
    }
}

fn crypto_aead_encrypt(c: &mut [u8], m: &[u8], ad: &[u8], npub: &[u8; 8], key: &Block) {
    let mut i = 0;
    let mut _in = 16;
    let mut out = 0;
    let mut remaining = m.len();

    let (mut w, mut block, mut lUp, mut lDown, mut checksum, mut LL) = (
        [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16],
    );

    AES_ENCRYPT(&mut LL, key);

    copy_block(&mut lUp, &LL);
    gf128_mul3(&mut lDown, &LL);
    let lDown2 = lDown;
    gf128_mul3(&mut lDown, &lDown2);

    mac(&mut w, ad, npub, &LL, key);

    while remaining > 16 {
        let lUp2 = lUp;
        gf128_mul2(&mut lUp, &lUp2);
        let lDown2 = lDown;
        gf128_mul2(&mut lDown, &lDown2);

        let checksum2 = checksum;
        xor_block(&mut checksum, &checksum2, m[.._in].try_into().expect("LOL"));
        xor_block(&mut block, m[.._in].try_into().expect("LOL"), &lUp);
        AES_ENCRYPT(&mut block, key);

        rho(&mut block, &mut w);

        AES_ENCRYPT(&mut block, key);

        xor_block(&mut c[out.._in], &block, &lDown);

        _in += 16;
        out += 16;
        remaining -= 16;
    }

    while i < remaining {
        checksum[i] ^= m[i];
        i += 1;
    }

    let lUp2 = lUp;
    gf128_mul7(&mut lUp, &lUp2);
    let lDown2 = lDown;
    gf128_mul7(&mut lDown, &lDown2);

    if remaining < 16 {
        checksum[i] ^= 0x80;
        let lUp2 = lUp;
        gf128_mul7(&mut lUp, &lUp2);
        let lDown2 = lDown;
        gf128_mul7(&mut lDown, &lDown2);
    }

    xor_block(&mut block, &checksum, &lUp);
    AES_ENCRYPT(&mut block, key);

    rho(&mut block, &mut w);

    AES_ENCRYPT(&mut block, key);
    xor_block(&mut c[out.._in], &block, &lDown);
    out += 16;

    if remaining == 0 {
        return;
    }

    let lUp2 = lUp;
    gf128_mul2(&mut lUp, &lUp2);
    let lDown2 = lDown;
    gf128_mul2(&mut lDown, &lDown2);

    xor_block(&mut block, &checksum, &lUp);
    AES_ENCRYPT(&mut block, key);

    rho(&mut block, &mut w);

    AES_ENCRYPT(&mut block, key);

    for i in 0..remaining {
        c[out + i] = block[i] ^ lDown[i];
    }
}

fn crypto_aead_decrypt(m: &mut [u8], c: &[u8], ad: &[u8], npub: &[u8; 8], key: &Block) {
    let mut _in = 16;
    let mut out = 0;
    let mut remaining = c.len() - 16;

    let (mut w, mut block, mut lUp, mut lDown, mut checksum, mut LL) = (
        [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16],
    );

    if c.len() < 16 {
        return
    }

    AES_ENCRYPT(&mut LL, key);
    copy_block(&mut lUp, &LL);
    gf128_mul3(&mut lDown, &LL);
    let lDown2 = lDown;
    gf128_mul3(&mut lDown, &lDown2);

    mac(&mut w, ad, npub, &LL, key);

    while remaining > 16 {
        let lUp2 = lUp;
        gf128_mul2(&mut lUp, &lUp2);
        let lDown2 = lDown;
        gf128_mul2(&mut lDown, &lDown2);

        xor_block(&mut block, c[out.._in].try_into().expect("LOL"), &lDown);
        AES_DECRYPT(&mut block, key);

        rho_inv(&mut block, &mut w);

        AES_DECRYPT(&mut block, key);
        xor_block(&mut m[out.._in], &block, &lUp);

        let checksum2 = checksum;
        xor_block(
            &mut checksum,
            &checksum2,
            m[out.._in].try_into().expect("LOL"),
        );

        _in += 16;
        out += 16;
        remaining -= 16;
    }

    let lUp2 = lUp;
    gf128_mul7(&mut lUp, &lUp2);
    let lDown2 = lDown;
    gf128_mul7(&mut lDown, &lDown2);

    if remaining < 16 {
        let lUp2 = lUp;
        gf128_mul7(&mut lUp, &lUp2);
        let lDown2 = lDown;
        gf128_mul7(&mut lDown, &lDown2);
    }

    xor_block(&mut block, c[out.._in].try_into().expect("LOL"), &lDown);
    AES_DECRYPT(&mut block, key);

    rho_inv(&mut block, &mut w);

    AES_DECRYPT(&mut block, key);
    let block2 = block;
    xor_block(&mut block, &block2, &lUp);

    let checksum2 = checksum;
    xor_block(&mut checksum, &checksum2, &block);

    // output last (maybe partial) plaintext block
    m[out..].copy_from_slice(&checksum[..remaining]);

    let lUp2 = lUp;
    gf128_mul2(&mut lUp, &lUp2);
    let lDown2 = lDown;
    gf128_mul2(&mut lDown, &lDown2);

    let block2 = block;
    xor_block(&mut block, &block2, &lUp);
    AES_ENCRYPT(&mut block, key);

    rho(&mut block, &mut w);

    AES_ENCRYPT(&mut block, key);
    let block2 = block;
    xor_block(&mut block, &block2, &lDown);

    if remaining < 16 {
        if checksum[remaining] != 0x80 {
            panic!("Decryption Error: Wrong checksum!");
        }
        for i in remaining + 1..16 {
            if checksum[i] != 0 {
                panic!("Decryption Error: Wrong checksum!");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extensive_test() {
        const MAX_PLAINTEXT: usize = 2048 + 1;
        let keys = [
            [0u8; 16],
            [
                0x2, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x3,
            ],
        ];
        let nonces = [[0u8; 8], [0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8]];
        let ad = [
        "",
		"0",
		"a",
		"ab",
		"0123456789abcde",
		"0123456789abcdef", // 16 bytes
		"0123456789abcdefg",
		"0123456789abcdefh",
		"0123456789abcdef0123456789abcde",
		"0123456789abcdef0123456789abcdef", // 32 bytes
		"0123456789abcdef0123456789abcdefg", // 33 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde", // 63 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef", // 64 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdeg", // 65 bytes
		// 127 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde",
		// 128 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		// 129 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdefi",
		// 255 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde",
		// 256 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		// 257 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdefx",
		// 512 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
	];
        let plaintexts = [
        "",
		"0",
		"a",
		"ab",
		"0123456789abcde",
		"0123456789abcdef", // 16 bytes
		"0123456789abcdefg",
		"0123456789abcdef0123456789abcde",
		"0123456789abcdef0123456789abcdef", // 32 bytes
		"0123456789abcdef0123456789abcdefg", // 33 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde", // 63 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef", // 64 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdeg", // 65 bytes
		// 127 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde",
		// 128 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		// 129 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdefi",
		// 255 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde",
		// 256 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		// 257 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdefx",
		// 512 bytes
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		// 2032 bytes = 127 blocks
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		// 2048 bytes = 128 blocks
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
		"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
    ];

        let mut c = [0u8; MAX_PLAINTEXT + 33];
        let mut m = [0u8; 2049];

        for n in 0..nonces.len() {
            for k in 0..keys.len() {
                for a in 0..ad.len() {
                    for p in 0..plaintexts.len() {
                        //FIXME: Here
                        let mut c = [0u8; plaintexts[p].len() + 16];
                        let mut m = [0u8; 2049];
                        println!("Verifying n={}, k={}, a={}, p={}", n, k, a, p);

                        println!("E+D ");
                        let len = plaintexts[p].len();
                        println!("adlen={}", ad[a].len());
                        println!("len={}", len);
                        crypto_aead_encrypt(
                            &mut c,
                            plaintexts[p].as_bytes(),
                            ad[a].as_bytes(),
                            &nonces[n],
                            &keys[k],
                        );
                        println!("clen={}", c.len());

                        crypto_aead_decrypt(&mut m, &c, ad[a].as_bytes(), &nonces[n], &keys[k]);
                        assert!(m.len() == len);
                        assert!(m == plaintexts[p].as_bytes());
                    }
                }
            }
        }

        println!("All {} combinations passed.", nonces.len() * keys.len() * ad.len() * plaintexts.len());
    }

    #[test]
    fn test_enc_single_block() {
        let m = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ];
        let mut c = [0u8; 32];
        let mut tag = [0u8; 16];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", m);
        crypto_aead_encrypt(&mut c, &m, &[0u8; 16], &[0u8; 8], &key);
        print!("Ciphertext: ");
        c.iter().for_each(|b| print!("{:02x?}", b));
        println!();
        tag[..].copy_from_slice(&c[16..]);
        print!("Tag: ");
        tag.iter().for_each(|b| print!("{:02x?}", b));
        println!();
        assert_eq!(
            [
                0x82, 0xf8, 0xbd, 0x31, 0xe0, 0x03, 0x55, 0xb5, 0x65, 0xaa, 0xfc, 0x8c, 0xf3, 0x0e,
                0x9b, 0x72, 0x7d, 0x68, 0xbc, 0x2d, 0x48, 0x46, 0x22, 0xf2, 0xc9, 0x19, 0xf5, 0x50,
                0xc6, 0x77, 0x8a, 0xe
            ],
            c
        );
        assert_eq!(
            [
                0x7d, 0x68, 0xbc, 0x2d, 0x48, 0x46, 0x22, 0xf2, 0xc9, 0x19, 0xf5, 0x50, 0xc6, 0x77,
                0x8a, 0xe
            ],
            tag
        );
    }

    #[test]
    fn test_enc_multi_block() {
        let m = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
            0xcc, 0xdd, 0xee, 0xff,
        ];
        let mut c = [0u8; 48];
        let mut tag = [0u8; 16];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", m);
        crypto_aead_encrypt(&mut c, &m, &[0u8; 16], &[0u8; 8], &key);
        print!("Ciphertext: ");
        c.iter().for_each(|b| print!("{:02x?}", b));
        println!();
        tag[..].copy_from_slice(&c[32..]);
        print!("Tag: ");
        tag.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0xa5, 0x3d, 0x91, 0x15, 0xb2, 0x97, 0x8, 0x3f, 0xaa, 0x14, 0x1c, 0x21, 0x21, 0xa9,
                0x93, 0x62, 0x4c, 0x3a, 0x78, 0x46, 0x86, 0x4b, 0x21, 0x15, 0x5d, 0x76, 0x11, 0x33,
                0xa9, 0x28, 0x9, 0x19, 0x2e, 0x10, 0xd8, 0xfd, 0xd1, 0x1f, 0x69, 0x22, 0x74, 0x66,
                0xe9, 0x1b, 0x1f, 0x18, 0x5e, 0xcd
            ],
            c
        );
        assert_eq!(
            [
                0x2e, 0x10, 0xd8, 0xfd, 0xd1, 0x1f, 0x69, 0x22, 0x74, 0x66, 0xe9, 0x1b, 0x1f, 0x18,
                0x5e, 0xcd
            ],
            tag
        );
    }

    #[test]
    fn test_enc_partial_block() {
        let m = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff, 0x00, 0x11,
        ];
        let mut c = [0u8; 34];
        let mut tag = [0u8; 16];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", m);
        crypto_aead_encrypt(&mut c, &m, &[0u8; 16], &[0u8; 8], &key);
        print!("Ciphertext: ");
        c.iter().for_each(|b| print!("{:02x?}", b));
        println!();
        tag[..2].copy_from_slice(&c[32..]);
        print!("Tag: ");
        tag.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0xa5, 0x3d, 0x91, 0x15, 0xb2, 0x97, 0x8, 0x3f, 0xaa, 0x14, 0x1c, 0x21, 0x21, 0xa9,
                0x93, 0x62, 0xa0, 0x60, 0x86, 0xa2, 0x13, 0xf0, 0x45, 0xb4, 0x72, 0x4f, 0x93, 0xda,
                0xfb, 0xdd, 0x9c, 0xff, 0x87, 0xc7
            ],
            c
        );
        assert_eq!(
            [0x87, 0xc7, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            tag
        );
    }

    #[test]
    fn test_enc_single_ad() {
        let m = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ];
        let ad = [
            0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,
            0x01, 0x00,
        ];
        let mut c = [0u8; 32];
        let mut tag = [0u8; 16];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", m);
        crypto_aead_encrypt(&mut c, &m, &ad, &[0u8; 8], &key);
        print!("Ciphertext: ");
        c.iter().for_each(|b| print!("{:02x?}", b));
        println!();
        tag[..].copy_from_slice(&c[16..]);
        print!("Tag: ");
        tag.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0x62, 0xed, 0x6f, 0xc1, 0xc, 0xfa, 0xb4, 0x1e, 0xd, 0xdc, 0x8c, 0xc0, 0x42, 0xef,
                0xc1, 0x31, 0xe3, 0x0, 0x9c, 0x36, 0x46, 0x13, 0x35, 0xcc, 0x9f, 0x18, 0x2a, 0xda,
                0x8f, 0xd3, 0x82, 0xd8
            ],
            c
        );
        assert_eq!(
            [
                0xe3, 0x0, 0x9c, 0x36, 0x46, 0x13, 0x35, 0xcc, 0x9f, 0x18, 0x2a, 0xda, 0x8f, 0xd3,
                0x82, 0xd8
            ],
            tag
        );
    }

    #[test]
    fn test_enc_multi_ad() {
        let m = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
            0xcc, 0xdd, 0xee, 0xff,
        ];
        let ad = [
            0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,
            0x01, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
            0x0c, 0x0d, 0x0e, 0x0f,
        ];
        let mut c = [0u8; 48];
        let mut tag = [0u8; 16];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", m);
        crypto_aead_encrypt(&mut c, &m, &ad, &[0u8; 8], &key);
        print!("Ciphertext: ");
        c.iter().for_each(|b| print!("{:#02x?},", b));
        println!();
        tag[..].copy_from_slice(&c[32..]);
        print!("Tag: ");
        tag.iter().for_each(|b| print!("{:#02x?},", b));
        println!();

        assert_eq!(
            [
                0x3b, 0xfc, 0x1b, 0xff, 0xc3, 0xb2, 0x1c, 0x1b, 0xb4, 0x6c, 0x20, 0xdd, 0x2e, 0xdf,
                0xfe, 0x99, 0x9d, 0x64, 0xfe, 0x1, 0x4d, 0xc8, 0x92, 0x1a, 0x61, 0x24, 0x49, 0x3e,
                0x4c, 0x90, 0x9c, 0x79, 0x74, 0xc5, 0x45, 0x74, 0x89, 0x5d, 0x9c, 0xd3, 0x70, 0x40,
                0x71, 0x15, 0x26, 0x4b, 0x8f, 0x98
            ],
            c
        );
        assert_eq!(
            [
                0x74, 0xc5, 0x45, 0x74, 0x89, 0x5d, 0x9c, 0xd3, 0x70, 0x40, 0x71, 0x15, 0x26, 0x4b,
                0x8f, 0x98
            ],
            tag
        );
    }

    #[test]
    fn test_enc_multi_nonce() {
        let m = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
            0xcc, 0xdd, 0xee, 0xff,
        ];
        let ad = [0x0; 16];
        let nonce = [0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08];
        let mut c = [0u8; 48];
        let mut tag = [0u8; 16];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", m);
        crypto_aead_encrypt(&mut c, &m, &ad, &nonce, &key);
        print!("Ciphertext: ");
        c.iter().for_each(|b| print!("{:#02x?},", b));
        println!();
        tag[..].copy_from_slice(&c[32..]);
        print!("Tag: ");
        tag.iter().for_each(|b| print!("{:#02x?},", b));
        println!();
    }

    #[test]
    fn test_dec_single_block() {
        let mut m = [0u8; 16];
        let c = [
            0x82, 0xf8, 0xbd, 0x31, 0xe0, 0x03, 0x55, 0xb5, 0x65, 0xaa, 0xfc, 0x8c, 0xf3, 0x0e,
            0x9b, 0x72, 0x7d, 0x68, 0xbc, 0x2d, 0x48, 0x46, 0x22, 0xf2, 0xc9, 0x19, 0xf5, 0x50,
            0xc6, 0x77, 0x8a, 0xe,
        ];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", c);
        crypto_aead_decrypt(&mut m, &c, &[0u8; 16], &[0u8; 8], &key);
        print!("Plaintext: ");
        m.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0x0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
                0xee, 0xff
            ],
            m
        );
    }

    #[test]
    fn test_dec_multi_block() {
        let mut m = [0u8; 32];
        let c = [
            0xa5, 0x3d, 0x91, 0x15, 0xb2, 0x97, 0x8, 0x3f, 0xaa, 0x14, 0x1c, 0x21, 0x21, 0xa9,
            0x93, 0x62, 0x4c, 0x3a, 0x78, 0x46, 0x86, 0x4b, 0x21, 0x15, 0x5d, 0x76, 0x11, 0x33,
            0xa9, 0x28, 0x9, 0x19, 0x2e, 0x10, 0xd8, 0xfd, 0xd1, 0x1f, 0x69, 0x22, 0x74, 0x66,
            0xe9, 0x1b, 0x1f, 0x18, 0x5e, 0xcd,
        ];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", c);
        crypto_aead_decrypt(&mut m, &c, &[0u8; 16], &[0u8; 8], &key);
        print!("Plaintext: ");
        m.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0x0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
                0xee, 0xff, 0x0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
                0xcc, 0xdd, 0xee, 0xff
            ],
            m
        );
    }

    #[test]
    fn test_dec_partial_block() {
        let mut m = [0u8; 18];
        let c = [
            0xa5, 0x3d, 0x91, 0x15, 0xb2, 0x97, 0x8, 0x3f, 0xaa, 0x14, 0x1c, 0x21, 0x21, 0xa9,
            0x93, 0x62, 0xa0, 0x60, 0x86, 0xa2, 0x13, 0xf0, 0x45, 0xb4, 0x72, 0x4f, 0x93, 0xda,
            0xfb, 0xdd, 0x9c, 0xff, 0x87, 0xc7,
        ];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", c);
        crypto_aead_decrypt(&mut m, &c, &[0u8; 16], &[0u8; 8], &key);
        print!("Plaintext: ");
        m.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0x0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
                0xee, 0xff, 0x0, 0x11
            ],
            m
        );
    }

    #[test]
    fn test_dec_single_ad() {
        let mut m = [0u8; 16];
        let ad = [
            0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,
            0x01, 0x01,
        ];
        let c = [
            0x7b, 0x90, 0x11, 0x25, 0x90, 0x17, 0x92, 0xa7, 0x18, 0x30, 0xc7, 0xa, 0x6d, 0x6d,
            0x61, 0x25, 0x49, 0xce, 0x54, 0x9d, 0x80, 0x0, 0x89, 0x37, 0x36, 0x1d, 0x41, 0xc1,
            0xa3, 0xdd, 0x62, 0x68,
        ];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", c);
        crypto_aead_decrypt(&mut m, &c, &ad, &[0u8; 8], &key);
        print!("Plaintext: ");
        m.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0x0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
                0xee, 0xff
            ],
            m
        );
    }

    #[test]
    fn test_dec_multi_ad() {
        let mut m = [0u8; 32];
        let ad = [
            0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,
            0x01, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
            0x0c, 0x0d, 0x0e, 0x0f,
        ];
        let c = [
            0x3b, 0xfc, 0x1b, 0xff, 0xc3, 0xb2, 0x1c, 0x1b, 0xb4, 0x6c, 0x20, 0xdd, 0x2e, 0xdf,
            0xfe, 0x99, 0x9d, 0x64, 0xfe, 0x1, 0x4d, 0xc8, 0x92, 0x1a, 0x61, 0x24, 0x49, 0x3e,
            0x4c, 0x90, 0x9c, 0x79, 0x74, 0xc5, 0x45, 0x74, 0x89, 0x5d, 0x9c, 0xd3, 0x70, 0x40,
            0x71, 0x15, 0x26, 0x4b, 0x8f, 0x98,
        ];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", c);
        crypto_aead_decrypt(&mut m, &c, &ad, &[0u8; 8], &key);
        print!("Plaintext: ");
        m.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
                0xee, 0xff, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
                0xcc, 0xdd, 0xee, 0xff
            ],
            m
        );
    }

    #[test]
    fn test_dec_multi_nonce() {
        let mut m = [0u8; 32];
        let ad = [0x0; 16];
        let nonce = [0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08];
        let c = [
            0x74, 0x26, 0x4a, 0x81, 0x99, 0xcb, 0xe5, 0xee, 0x83, 0xed, 0x3a, 0x1e, 0x1c, 0xfd,
            0x98, 0x8e, 0xd9, 0xac, 0x12, 0x49, 0x2c, 0x1a, 0xb4, 0xd2, 0x3a, 0x7f, 0x5a, 0x5b,
            0xf7, 0x38, 0x19, 0x11, 0x64, 0xc5, 0xda, 0xf, 0x2d, 0x7f, 0xe7, 0xc2, 0x53, 0xbf,
            0x97, 0x36, 0xee, 0x58, 0x3b, 0xa0,
        ];
        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ];

        println!("Input: {:?}", c);
        crypto_aead_decrypt(&mut m, &c, &ad, &nonce, &key);
        print!("Plaintext: ");
        m.iter().for_each(|b| print!("{:02x?}", b));
        println!();

        assert_eq!(
            [
                0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
                0xee, 0xff, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
                0xcc, 0xdd, 0xee, 0xff
            ],
            m
        );
    }
}
