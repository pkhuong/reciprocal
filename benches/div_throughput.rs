use criterion::black_box;
use criterion::criterion_group;
use criterion::Criterion;

const ITER: usize = 10000;
const OFFSET: u64 = 0x9f1668016f482246;
const MULTIPLIER: u64 = 0xf6ee9cc7a7f7d033;

fn generate(i: usize) -> u64 {
    (i as u64).wrapping_mul(MULTIPLIER).wrapping_add(OFFSET)
}

fn hardware_u64_div<const D: u64>(c: &mut Criterion) {
    let inputs: Vec<u64> = (0..ITER).map(generate).collect();

    c.bench_function(&format!("hardware_u64_div_{}", D), move |b| {
        b.iter(|| {
            let mut sum = 0;
            let div = black_box(D);
            for i in black_box(&inputs) {
                sum += i / div;
            }

            black_box(sum)
        })
    });
}

fn compiled_u64_div<const D: u64>(c: &mut Criterion) {
    let inputs: Vec<u64> = (0..ITER).map(generate).collect();

    c.bench_function(&format!("compiled_u64_div_by_{}", D), move |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in black_box(&inputs) {
                sum += i / D;
            }

            black_box(sum)
        })
    });
}

fn partial_reciprocal_sat_u64_div<const D: u64>(c: &mut Criterion) {
    use reciprocal::PartialReciprocal;

    let d = black_box(PartialReciprocal::new(D).unwrap());
    let inputs: Vec<u64> = (0..ITER).map(generate).collect();

    c.bench_function(&format!("partial_sat_u64_div_by_{}", D), move |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in black_box(&inputs) {
                sum += d.apply_saturating(*i);
            }

            black_box(sum)
        })
    });
}

fn partial_reciprocal_of_u64_div<const D: u64>(c: &mut Criterion) {
    use reciprocal::PartialReciprocal;

    let d = black_box(PartialReciprocal::new(D).unwrap());
    let inputs: Vec<u64> = (0..ITER).map(generate).collect();

    c.bench_function(&format!("partial_of_u64_div_by_{}", D), move |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in black_box(&inputs) {
                sum += d.apply_overflowing(*i);
            }

            black_box(sum)
        })
    });
}

fn reciprocal_full_u64_div<const D: u64>(c: &mut Criterion) {
    use reciprocal::PartialReciprocal;

    let d = black_box(PartialReciprocal::new(D).unwrap());
    let inputs: Vec<u64> = (0..ITER).map(generate).collect();

    c.bench_function(&format!("reciprocal_u64_div_by_{}", D), move |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in black_box(&inputs) {
                sum += d.apply(*i);
            }

            black_box(sum)
        })
    });
}

fn strength_reduce_u64_div<const D: u64>(c: &mut Criterion) {
    use strength_reduce::StrengthReducedU64;

    let d = black_box(StrengthReducedU64::new(D));
    let inputs: Vec<u64> = (0..ITER).map(generate).collect();

    c.bench_function(&format!("strength_reduce_u64_div_by_{}", D), move |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in black_box(&inputs) {
                sum += *i / d;
            }

            black_box(sum)
        })
    });
}

fn fast_divide_u64_div<const D: u64>(c: &mut Criterion) {
    use fastdivide::DividerU64;

    let d = black_box(DividerU64::divide_by(D));
    let inputs: Vec<u64> = (0..ITER).map(generate).collect();

    c.bench_function(&format!("fast_divide_u64_div_by_{}", D), move |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in black_box(&inputs) {
                sum += d.divide(*i);
            }

            black_box(sum)
        })
    });
}

macro_rules! u64_div {
    ($name:ident, $div:literal) => {
        criterion_group!(
            $name,
            hardware_u64_div<{ $div }>,
            compiled_u64_div<{ $div }>,
            partial_reciprocal_sat_u64_div<{ $div }>,
            partial_reciprocal_of_u64_div<{ $div }>,
            reciprocal_full_u64_div<{ $div }>,
            strength_reduce_u64_div<{ $div }>,
            fast_divide_u64_div<{ $div }>,
        );
    };
}

u64_div!(u64_div_by_2, 2);
u64_div!(u64_div_by_7, 7);
u64_div!(u64_div_by_11, 11);

criterion::criterion_main!(u64_div_by_2, u64_div_by_7, u64_div_by_11);
