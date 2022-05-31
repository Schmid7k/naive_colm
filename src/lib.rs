mod aes;

use aes::{BlockBuf, AES_DECRYPT, AES_ENCRYPT};

pub type Block = [u8; 16];

fn xor_block(buf: BlockBuf, a: &[u8]) {
    match buf {
        BlockBuf::InPlace(in_out) => {
            for i in 0..16 {
                in_out[i] ^= a[i];
            }
        },
        BlockBuf::FromTo((_in, out)) => {
            for i in 0..16 {
                out[i] = _in[i] ^ a[i];
            }
        }
    }
}

fn copy_block(dest: &mut [u8], src: &[u8]) {
    dest[..16].copy_from_slice(&src[..16]);
}

fn shl_block(buf: BlockBuf) {
    match buf {
        BlockBuf::InPlace(in_out) => {
            for i in 0..15 {
                in_out[i] = (in_out[i] << 1) | (in_out[i + 1] >> 7);
            }
            in_out[15] <<= 1;
        }
        BlockBuf::FromTo((_in, out)) => {
            for i in 0..15 {
                out[i] = (_in[i] << 1) | (_in[i + 1] >> 7);
            }
            out[15] = _in[15] << 1;
        }
    }
}

fn gf128_mul2(buf: BlockBuf) {
    match buf {
        BlockBuf::InPlace(in_out) => {
            let msb = in_out[0] & 0x80;
            shl_block(BlockBuf::InPlace(in_out));
            if msb > 0 {
                in_out[15] ^= 0x87;
            }
        }
        BlockBuf::FromTo((_in, out)) => {
            let msb = _in[0] & 0x80;
            shl_block(BlockBuf::FromTo((_in, out)));
            if msb > 0 {
                out[15] ^= 0x87;
            }
        }
    }
}

fn gf128_mul3(buf: BlockBuf) {
    let mut b = [0u8; 16];
    match buf {
        BlockBuf::InPlace(in_out) => {
            gf128_mul2(BlockBuf::FromTo((in_out, &mut b)));
            xor_block(BlockBuf::InPlace(in_out), &b);
        },
        BlockBuf::FromTo((_in, out)) => {
            gf128_mul2(BlockBuf::FromTo((_in, &mut b)));
            xor_block(BlockBuf::FromTo((&b, out)), _in);
        }
    }
}

fn gf128_mul7(buf: BlockBuf) {
    let mut b = [0u8; 16];
    let mut c = [0u8; 16];
    match buf {
        BlockBuf::InPlace(in_out) => {
            gf128_mul2(BlockBuf::FromTo((in_out, &mut b)));
            gf128_mul2(BlockBuf::FromTo((&b, &mut c)));
            xor_block(BlockBuf::InPlace(&mut c), &in_out);
            xor_block(BlockBuf::InPlace(in_out), &c);
        },
        BlockBuf::FromTo((_in, out)) => {
            gf128_mul2(BlockBuf::FromTo((_in, &mut b)));
            gf128_mul2(BlockBuf::FromTo((&b, &mut c)));
            xor_block(BlockBuf::InPlace(&mut c), _in);
            xor_block(BlockBuf::FromTo((&c, out)), _in);
        }
    }
}

fn rho(block: &mut Block, w: &mut Block) {
    let mut new_w = [0u8; 16];
    gf128_mul2(BlockBuf::FromTo((w, &mut new_w)));
    xor_block(BlockBuf::InPlace(&mut new_w), block);
    xor_block(BlockBuf::FromTo((&new_w, block)), w);
    copy_block(w, &new_w)
}

fn rho_inv(block: &mut Block, w: &mut Block) {
    let mut new_w = [0u8; 16];
    gf128_mul2(BlockBuf::FromTo((w, &mut new_w)));
    xor_block(BlockBuf::InPlace(w), block);
    xor_block(BlockBuf::FromTo((&new_w, block)), w);
}

fn mac(out: &mut [u8], _in: &[u8], nonce: &[u8; 8], ll: &Block, key: &Block) {
    let (mut v, mut delta, mut block) = ([0u8; 16], [0u8; 16], [0u8; 16]);
    let mut i = 0;
    let mut len = _in.len();
    let mut previous = 0;
    let mut current = 16;

    gf128_mul3(BlockBuf::FromTo((ll, &mut delta)));
    v[..8].copy_from_slice(&nonce[..]);
    xor_block(BlockBuf::InPlace(&mut v), &delta);

    AES_ENCRYPT(&mut v, key);

    while len >= 16 {
        gf128_mul2(BlockBuf::InPlace(&mut delta));
        xor_block(BlockBuf::FromTo((&_in[previous..current], &mut block)), &delta);
        AES_ENCRYPT(&mut block, key);

        xor_block(BlockBuf::InPlace(&mut v), &block);

        previous += 16;
        current += 16;
        len -= 16;
    }

    if len > 0 {
        gf128_mul7(BlockBuf::FromTo((&delta, &mut block)));
        while i < len {
            block[i] ^= _in[i];
            i += 1;
        }
        block[len] ^= 0x80;
        AES_ENCRYPT(&mut block, key);
        xor_block(BlockBuf::FromTo((&v, out)), &block);
    } else {
        copy_block(out, &v);
    }
}

fn crypto_aead_encrypt(c: &mut [u8], m: &[u8], ad: &[u8], npub: &[u8; 8], key: &Block) {
    let mut i = 0;
    let mut _in = 16;
    let mut out = 0;
    let mut remaining = m.len();

    let (mut w, mut block, mut l_up, mut l_down, mut checksum, mut ll) = (
        [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16],
    );

    AES_ENCRYPT(&mut ll, key);

    copy_block(&mut l_up, &ll);
    gf128_mul3(BlockBuf::FromTo((&ll, &mut l_down)));
    gf128_mul3(BlockBuf::InPlace(&mut l_down));

    mac(&mut w, ad, npub, &ll, key);

    while remaining > 16 {
        gf128_mul2(BlockBuf::InPlace(&mut l_up));
        gf128_mul2(BlockBuf::InPlace(&mut l_down));

        xor_block(BlockBuf::InPlace(&mut checksum), &m[out.._in]);
        xor_block(BlockBuf::FromTo((&m[out.._in], &mut block)), &l_up);
        AES_ENCRYPT(&mut block, key);

        rho(&mut block, &mut w);

        AES_ENCRYPT(&mut block, key);

        xor_block(BlockBuf::FromTo((&block, &mut c[out.._in])), &l_down);

        _in += 16;
        out += 16;
        remaining -= 16;
    }

    while i < remaining {
        checksum[i] ^= m[i];
        i += 1;
    }

    gf128_mul7(BlockBuf::InPlace(&mut l_up));
    gf128_mul7(BlockBuf::InPlace(&mut l_down));

    if remaining < 16 {
        checksum[i] ^= 0x80;
        gf128_mul7(BlockBuf::InPlace(&mut l_up));
        gf128_mul7(BlockBuf::InPlace(&mut l_down));
    }

    xor_block(BlockBuf::FromTo((&checksum, &mut block)), &l_up);
    AES_ENCRYPT(&mut block, key);

    rho(&mut block, &mut w);

    AES_ENCRYPT(&mut block, key);
    xor_block(BlockBuf::FromTo((&block, &mut c[out.._in])), &l_down);
    out += 16;

    if remaining == 0 {
        return;
    }

    gf128_mul2(BlockBuf::InPlace(&mut l_up));
    gf128_mul2(BlockBuf::InPlace(&mut l_down));

    xor_block(BlockBuf::FromTo((&checksum, &mut block)), &l_up);
    AES_ENCRYPT(&mut block, key);

    rho(&mut block, &mut w);

    AES_ENCRYPT(&mut block, key);

    for i in 0..remaining {
        c[out + i] = block[i] ^ l_down[i];
    }
}

fn crypto_aead_decrypt(m: &mut [u8], c: &[u8], ad: &[u8], npub: &[u8; 8], key: &Block) {
    let mut _in = 16;
    let mut out = 0;
    let mut remaining = c.len() - 16;

    let (mut w, mut block, mut l_up, mut l_down, mut checksum, mut ll) = (
        [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16],
    );

    if c.len() < 16 {
        return;
    }

    AES_ENCRYPT(&mut ll, key);
    copy_block(&mut l_up, &ll);
    gf128_mul3(BlockBuf::FromTo((&ll, &mut l_down)));
    gf128_mul3(BlockBuf::InPlace(&mut l_down));

    mac(&mut w, ad, npub, &ll, key);

    while remaining > 16 {
        gf128_mul2(BlockBuf::InPlace(&mut l_up));
        gf128_mul2(BlockBuf::InPlace(&mut l_down));

        xor_block(BlockBuf::FromTo((&c[out.._in], &mut block)), &l_down);
        AES_DECRYPT(&mut block, key);

        rho_inv(&mut block, &mut w);

        AES_DECRYPT(&mut block, key);
        xor_block(BlockBuf::FromTo((&block, &mut m[out.._in])), &l_up);

        xor_block(BlockBuf::InPlace(&mut checksum), &m[out.._in]);

        _in += 16;
        out += 16;
        remaining -= 16;
    }

    gf128_mul7(BlockBuf::InPlace(&mut l_up));
    gf128_mul7(BlockBuf::InPlace(&mut l_down));

    if remaining < 16 {
        gf128_mul7(BlockBuf::InPlace(&mut l_up));
        gf128_mul7(BlockBuf::InPlace(&mut l_down));
    }

    xor_block(BlockBuf::FromTo((&c[out.._in], &mut block)), &l_down);
    AES_DECRYPT(&mut block, key);

    rho_inv(&mut block, &mut w);

    AES_DECRYPT(&mut block, key);
    xor_block(BlockBuf::InPlace(&mut block), &l_up);

    xor_block(BlockBuf::InPlace(&mut checksum), &block);

    // output last (maybe partial) plaintext block
    m[out..].copy_from_slice(&checksum[..remaining]);

    gf128_mul2(BlockBuf::InPlace(&mut l_up));
    gf128_mul2(BlockBuf::InPlace(&mut l_down));

    xor_block(BlockBuf::InPlace(&mut block), &l_up);
    AES_ENCRYPT(&mut block, key);

    rho(&mut block, &mut w);

    AES_ENCRYPT(&mut block, key);
    xor_block(BlockBuf::InPlace(&mut block), &l_down);

    if remaining < 16 {
        if checksum[remaining] != 0x80 {
            panic!("Decryption Error: Wrong checksum!");
        }
        for i in checksum.iter().skip(remaining + 1) {
            if *i != 0 {
                panic!("Decryption Error: Wrong checksum!");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extensive_test_suite() {
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
            0, 1, 2, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257, 511, 512,
            513, 1023, 1024, 1025, 2032, 2047, 2048, 2049,
        ];

        for (n, nonce) in nonces.iter().enumerate() {
            for (k, key) in keys.iter().enumerate() {
                for (a, ad) in ad.iter().enumerate() {
                    for size in &plaintexts {
                        let mut m = vec![0; *size];
                        let mut c = vec![0; *size + 16];
                        println!("Verifying n={}, k={}, a={}, p={}", n, k, a, size);

                        println!("E+D ");
                        println!("adlen={}", ad.len());
                        println!("len={}", m.len());
                        crypto_aead_encrypt(&mut c, &m, ad.as_bytes(), nonce, key);
                        println!("clen={}", c.len());

                        crypto_aead_decrypt(&mut m, &c, ad.as_bytes(), nonce, key);

                        assert!(m == vec![0; *size]);
                    }
                }
            }
        }

        println!(
            "All {} combinations passed.",
            nonces.len() * keys.len() * ad.len() * plaintexts.len()
        );
    }
}
