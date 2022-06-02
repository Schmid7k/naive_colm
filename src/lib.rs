use aes::cipher::{generic_array::GenericArray, BlockDecrypt, BlockEncrypt, KeyInit};
use aes::{Aes128Dec, Aes128Enc};

pub type Block = [u8; 16];

fn xor_block(a: &[u8], b: &[u8]) -> [u8; 16] {
    assert!(a.len() == 16 && b.len() == 16);
    let mut res = [0u8; 16];
    for i in 0..16 {
        res[i] = a[i] ^ b[i];
    }

    res
}

fn copy_block(src: &[u8]) -> [u8; 16] {
    assert!(src.len() == 16);
    let mut res = [0u8; 16];
    res[..16].copy_from_slice(&src[..16]);
    res
}

fn shl_block(a: &[u8]) -> [u8; 16] {
    assert!(a.len() == 16);
    let mut res = [0u8; 16];
    for i in 0..15 {
        res[i] = (a[i] << 1) | (a[i + 1] >> 7);
    }
    res[15] = a[15] << 1;

    res
}

fn gf128_mul2(x: &[u8]) -> [u8; 16] {
    assert!(x.len() == 16);
    let msb = x[0] & 0x80;
    let mut res = shl_block(x);
    if msb > 0 {
        res[15] ^= 0x87;
    }
    res
}

fn gf128_mul3(x: &[u8]) -> [u8; 16] {
    assert!(x.len() == 16);
    let b = gf128_mul2(x);
    xor_block(x, &b)
}

fn gf128_mul7(x: &[u8]) -> [u8; 16] {
    assert!(x.len() == 16);
    let b = gf128_mul2(x);
    let mut c = gf128_mul2(&b);
    c = xor_block(&c, &b);
    xor_block(&c, x)
}

fn rho(block: &mut Block, w: &mut Block) {
    assert!(block.len() == 16 && w.len() == 16);
    let mut new_w = gf128_mul2(w);
    new_w = xor_block(&new_w, block);
    *block = xor_block(&new_w, w);
    *w = copy_block(&new_w);
}

fn rho_inv(block: &mut Block, w: &mut Block) {
    assert!(block.len() == 16 && w.len() == 16);
    let new_w = gf128_mul2(w);
    *w = xor_block(w, block);
    *block = xor_block(&new_w, w);
}

fn mac(out: &mut [u8], _in: &[u8], nonce: &[u8; 8], ll: &Block, key: &Block) {
    let cipher = Aes128Enc::new(&GenericArray::from(*key));
    let mut block: [u8; 16];
    let mut v = [0u8; 16];
    let mut i = 0;
    let mut len = _in.len();
    let mut previous = 0;
    let mut current = 16;

    let mut delta = gf128_mul3(ll);
    v[..8].copy_from_slice(&nonce[..]);
    v = xor_block(&v, &delta);

    cipher.encrypt_block(&mut GenericArray::from(v));

    while len >= 16 {
        delta = gf128_mul2(&delta);
        block = xor_block(&_in[previous..current], &delta);
        cipher.encrypt_block(&mut GenericArray::from(block));

        v = xor_block(&v, &block);

        previous += 16;
        current += 16;
        len -= 16;
    }

    if len > 0 {
        block = gf128_mul7(&delta);
        while i < len {
            block[i] ^= _in[i];
            i += 1;
        }
        block[len] ^= 0x80;
        cipher.encrypt_block(&mut GenericArray::from(block));
        out.copy_from_slice(&xor_block(&v, &block));
    } else {
        out.copy_from_slice(&v);
    }
}

pub fn crypto_aead_encrypt(c: &mut [u8], m: &[u8], ad: &[u8], npub: &[u8; 8], key: &Block) {
    let cipher = Aes128Enc::new(&GenericArray::from(*key));
    let mut i = 0;
    let mut _in = 16;
    let mut out = 0;
    let mut remaining = m.len();

    let ll = [0u8; 16];
    let mut block: [u8; 16];
    let mut checksum = [0u8; 16];
    let mut w = [0u8; 16];

    cipher.encrypt_block(&mut GenericArray::from(ll));

    let mut l_up = copy_block(&ll);
    let mut l_down = gf128_mul3(&ll);
    l_down = gf128_mul3(&l_down);

    mac(&mut w, ad, npub, &ll, key);

    while remaining > 16 {
        l_up = gf128_mul2(&l_up);
        l_down = gf128_mul2(&l_down);

        checksum = xor_block(&checksum, &m[out.._in]);
        block = xor_block(&m[out.._in], &l_up);

        cipher.encrypt_block(&mut GenericArray::from(block));

        rho(&mut block, &mut w);

        cipher.encrypt_block(&mut GenericArray::from(block));

        c[out.._in].copy_from_slice(&xor_block(&block, &l_down));

        _in += 16;
        out += 16;
        remaining -= 16;
    }

    while i < remaining {
        checksum[i] ^= m[out..][i];
        i += 1;
    }

    l_up = gf128_mul7(&l_up);
    l_down = gf128_mul7(&l_down);

    if remaining < 16 {
        checksum[i] ^= 0x80;
        l_up = gf128_mul7(&l_up);
        l_down = gf128_mul7(&l_down);
    }

    block = xor_block(&checksum, &l_up);
    cipher.encrypt_block(&mut GenericArray::from(block));

    rho(&mut block, &mut w);

    cipher.encrypt_block(&mut GenericArray::from(block));
    c[out.._in].copy_from_slice(&xor_block(&block, &l_down));
    out += 16;

    if remaining == 0 {
        return;
    }

    l_up = gf128_mul2(&l_up);
    l_down = gf128_mul2(&l_down);

    block = xor_block(&checksum, &l_up);
    cipher.encrypt_block(&mut GenericArray::from(block));

    rho(&mut block, &mut w);

    cipher.encrypt_block(&mut GenericArray::from(block));

    for i in 0..remaining {
        c[out + i] = block[i] ^ l_down[i];
    }
}

pub fn crypto_aead_decrypt(m: &mut [u8], c: &[u8], ad: &[u8], npub: &[u8; 8], key: &Block) {
    assert!(c.len() >= 16);
    let cipher_enc = Aes128Enc::new(&GenericArray::from(*key));
    let cipher_dec = Aes128Dec::new(&GenericArray::from(*key));
    let mut _in = 16;
    let mut out = 0;
    let mut remaining = c.len() - 16;

    let ll = [0u8; 16];
    let mut block: [u8; 16];
    let mut w = [0u8; 16];
    let mut checksum = [0u8; 16];

    cipher_enc.encrypt_block(&mut GenericArray::from(ll));
    let mut l_up = copy_block(&ll);
    let mut l_down = gf128_mul3(&ll);
    l_down = gf128_mul3(&l_down);

    mac(&mut w, ad, npub, &ll, key);

    while remaining > 16 {
        l_up = gf128_mul2(&l_up);
        l_down = gf128_mul2(&l_down);

        block = xor_block(&c[out.._in], &l_down);
        cipher_dec.decrypt_block(&mut GenericArray::from(block));

        rho_inv(&mut block, &mut w);

        cipher_dec.decrypt_block(&mut GenericArray::from(block));
        m[out.._in].copy_from_slice(&xor_block(&block, &l_up));

        checksum = xor_block(&checksum, &m[out.._in]);

        _in += 16;
        out += 16;
        remaining -= 16;
    }

    l_up = gf128_mul7(&l_up);
    l_down = gf128_mul7(&l_down);

    if remaining < 16 {
        l_up = gf128_mul7(&l_up);
        l_down = gf128_mul7(&l_down);
    }

    block = xor_block(&c[out.._in], &l_down);
    cipher_dec.decrypt_block(&mut GenericArray::from(block));

    rho_inv(&mut block, &mut w);

    cipher_dec.decrypt_block(&mut GenericArray::from(block));
    block = xor_block(&block, &l_up);

    checksum = xor_block(&checksum, &block);

    // output last (maybe partial) plaintext block
    m[out..].copy_from_slice(&checksum[..remaining]);

    //FIXME: What is this part for:
    //<----
    l_up = gf128_mul2(&l_up);
    l_down = gf128_mul2(&l_down);

    block = xor_block(&block, &l_up);
    cipher_enc.encrypt_block(&mut GenericArray::from(block));

    rho(&mut block, &mut w);

    cipher_enc.encrypt_block(&mut GenericArray::from(block));
    block = xor_block(&block, &l_down);
    //---->

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
