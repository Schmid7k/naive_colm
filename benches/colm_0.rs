mod utils;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use criterion_cycles_per_byte::CyclesPerByte;
use naive_colm::crypto_aead_encrypt;
use utils::{AD, KEYS, NONCES, PLAINTEXTS};

fn bench(c: &mut Criterion<CyclesPerByte>) {
    let mut group = c.benchmark_group("colm-0");

    for nonce in NONCES.iter() {
        for key in KEYS.iter() {
            for ad in AD.iter().map(|s| s.as_bytes()) {
                for m in PLAINTEXTS.iter().map(|s| s.as_bytes()) {
                    let size = m.len();
                    let mut c = vec![0; size + 16];

                    group.throughput(Throughput::Bytes(size as u64));

                    group.bench_function(BenchmarkId::new("encrypt-simple", size), |b| {
                        b.iter(|| crypto_aead_encrypt(&mut c, m, ad, nonce, key));
                    });
                }
            }
        }
    }

    group.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default().with_measurement(CyclesPerByte);
    targets = bench
);

criterion_main!(benches);
