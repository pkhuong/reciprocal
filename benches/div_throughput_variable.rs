use criterion::black_box;
use criterion::criterion_group;
use criterion::Criterion;

const ITER: usize = 10000;
const OFFSET: u64 = 0x9f1668016f482246;
const MULTIPLIER: u64 = 0xf6ee9cc7a7f7d033;

const DIVISORS: [u64; 4] = [2, 3, 7, 11];

fn generate(i: usize) -> u64 {
    (i as u64).wrapping_mul(MULTIPLIER).wrapping_add(OFFSET)
}

fn generate_div_indices(n: usize) -> Vec<usize> {
    use rand::distributions::Distribution;
    use rand::SeedableRng;

    let range = rand::distributions::Uniform::<usize>::new(0, DIVISORS.len());
    let mut rand: rand_chacha::ChaChaRng = SeedableRng::seed_from_u64(1);

    (0..n).map(|_| range.sample(&mut rand)).collect()
}

fn hardware_u64_div(c: &mut Criterion) {
    let inputs: Vec<u64> = (0..ITER).map(generate).collect();
    let divisors: Vec<u64> = generate_div_indices(ITER)
        .iter()
        .map(|i| DIVISORS[*i])
        .collect();

    c.bench_function("hardware_u64_div", move |b| {
        b.iter(|| {
            let mut sum = 0;
            for (i, div) in black_box(&inputs).iter().zip(black_box(&divisors)) {
                sum += i / div;
            }

            black_box(sum)
        })
    });
}

fn partial_u64_div(c: &mut Criterion) {
    use reciprocal::PartialReciprocal;

    let inputs: Vec<u64> = (0..ITER).map(generate).collect();
    let reciprocals: Vec<_> = DIVISORS
        .iter()
        .map(|i| PartialReciprocal::new(*i).unwrap())
        .collect();
    let divisors: Vec<&PartialReciprocal> = generate_div_indices(ITER)
        .iter()
        .map(|i| &reciprocals[*i])
        .collect();

    c.bench_function("partial_u64_div", move |b| {
        b.iter(|| {
            let mut sum = 0;
            for (i, div) in black_box(&inputs).iter().zip(black_box(&divisors)) {
                sum += div.apply(*i);
            }

            black_box(sum)
        })
    });
}

fn reciprocal_u64_div(c: &mut Criterion) {
    use reciprocal::Reciprocal;

    let inputs: Vec<u64> = (0..ITER).map(generate).collect();
    let reciprocals: Vec<_> = DIVISORS
        .iter()
        .map(|i| Reciprocal::new(*i).unwrap())
        .collect();
    let divisors: Vec<&Reciprocal> = generate_div_indices(ITER)
        .iter()
        .map(|i| &reciprocals[*i])
        .collect();

    c.bench_function("reciprocal_u64_div", move |b| {
        b.iter(|| {
            let mut sum = 0;
            for (i, div) in black_box(&inputs).iter().zip(black_box(&divisors)) {
                sum += div.apply(*i);
            }

            black_box(sum)
        })
    });
}

fn strength_reduce_u64_div(c: &mut Criterion) {
    use strength_reduce::StrengthReducedU64;

    let inputs: Vec<u64> = (0..ITER).map(generate).collect();
    let reciprocals: Vec<_> = DIVISORS
        .iter()
        .map(|i| StrengthReducedU64::new(*i))
        .collect();
    let divisors: Vec<&StrengthReducedU64> = generate_div_indices(ITER)
        .iter()
        .map(|i| &reciprocals[*i])
        .collect();

    c.bench_function("strength_reduce_u64_div", move |b| {
        b.iter(|| {
            let mut sum = 0;
            for (i, div) in black_box(&inputs).iter().zip(black_box(&divisors)) {
                sum += *i / **div;
            }

            black_box(sum)
        })
    });
}

fn fast_divide_u64_div(c: &mut Criterion) {
    use fastdivide::DividerU64;

    let inputs: Vec<u64> = (0..ITER).map(generate).collect();
    let reciprocals: Vec<_> = DIVISORS.iter().map(|i| DividerU64::divide_by(*i)).collect();
    let divisors: Vec<&DividerU64> = generate_div_indices(ITER)
        .iter()
        .map(|i| &reciprocals[*i])
        .collect();

    c.bench_function("fast_divide_u64_div", move |b| {
        b.iter(|| {
            let mut sum = 0;
            for (i, div) in black_box(&inputs).iter().zip(black_box(&divisors)) {
                sum += div.divide(*i);
            }

            black_box(sum)
        })
    });
}

criterion_group!(
    u64_div_variable,
    hardware_u64_div,
    partial_u64_div,
    reciprocal_u64_div,
    strength_reduce_u64_div,
    fast_divide_u64_div
);

criterion::criterion_main!(u64_div_variable);
