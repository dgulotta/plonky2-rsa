use std::marker::PhantomData;

use anyhow::anyhow;
use num::{BigUint, Integer, Zero};
use plonky2::{
    field::{
        extension::Extendable,
        goldilocks_field::GoldilocksField,
        types::{Field, Field64, PrimeField, PrimeField64},
    },
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CommonCircuitData},
    util::serialization::{Buffer, IoResult, Read, Write},
};
use plonky2_gate_utils::SimpleGate;
use plonky2_u32::gadgets::multiple_comparison::list_le_circuit;

#[derive(Debug, Default, Clone, serde::Serialize, serde::Deserialize)]
pub struct BigUintTarget<const BITS: usize> {
    pub limbs: Vec<Target>,
}

impl<const BITS: usize> BigUintTarget<BITS> {
    fn num_limbs(&self) -> usize {
        self.limbs.len()
    }
}

pub trait CircuitBuilderBigUint<F: RichField + Extendable<D>, const D: usize, const BITS: usize> {
    fn add_virtual_biguint_target(&mut self, n_limbs: usize) -> BigUintTarget<BITS>;
    fn constant_biguint(&mut self, value: &BigUint) -> BigUintTarget<BITS>;
    fn zero_biguint(&mut self) -> BigUintTarget<BITS> {
        self.constant_biguint(&BigUint::ZERO)
    }
    fn add_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;
    fn mul_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;
    fn connect_biguint(&mut self, a: &BigUintTarget<BITS>, b: &BigUintTarget<BITS>);
    fn div_rem_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> (BigUintTarget<BITS>, BigUintTarget<BITS>);
    fn div_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        self.div_rem_biguint(a, b).0
    }
    fn rem_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        self.div_rem_biguint(a, b).1
    }
    fn mul_add_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
        c: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let prod = self.mul_biguint(a, b);
        self.add_biguint(&prod, c)
    }
    fn le_biguint(&mut self, a: &BigUintTarget<BITS>, b: &BigUintTarget<BITS>) -> BoolTarget;
    fn if_biguint(
        &mut self,
        condition: BoolTarget,
        then_t: &BigUintTarget<BITS>,
        else_t: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;
}

pub fn split_biguint<const BITS: usize>(x: &BigUint) -> Vec<u32> {
    let n_limbs = x.bits().div_ceil(BITS as u64) as usize;
    let mut ans = Vec::with_capacity(n_limbs);
    let mut it = x.iter_u32_digits();
    let mut leftover = 0;
    let mut leftover_bits = 0;
    let full_mask = (1 << BITS) - 1;
    while ans.len() < n_limbs {
        if leftover_bits >= BITS {
            ans.push(leftover & full_mask);
            leftover >>= BITS;
            leftover_bits -= BITS;
        } else {
            let low = leftover;
            leftover = it.next().unwrap_or(0);
            let high_bits = BITS - leftover_bits;
            let mask = (1 << high_bits) - 1;
            let high = leftover & mask;
            ans.push(low | (high << leftover_bits));
            leftover >>= high_bits;
            leftover_bits = 32 - high_bits;
        }
    }
    ans
}

fn carry_mut<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    low: &mut Target,
    high: &mut Target,
    low_bits: usize,
    total_bits: usize,
) {
    let (l, h) = builder.split_low_high(*low, low_bits, total_bits);
    *low = l;
    *high = builder.add(*high, h);
}

pub trait CircuitBuilderBigUintFromField<const BITS: usize> {
    fn field_to_biguint(&mut self, a: Target) -> BigUintTarget<BITS>;
}

impl<const BITS: usize> CircuitBuilderBigUintFromField<BITS>
    for CircuitBuilder<GoldilocksField, 2>
{
    fn field_to_biguint(&mut self, a: Target) -> BigUintTarget<BITS> {
        assert!(BITS >= 22);
        let (low, high) = self.split_low_high(a, 32, 64);
        // make sure that low = 0 if high = 2^32 - 1
        let max = self.constant(GoldilocksField::from_canonical_i64(0xFFFFFFFF));
        let high_minus_max = self.sub(high, max);
        conditional_zero(self, high_minus_max, low);
        let (out_low, out_mid1) = self.split_low_high(low, BITS, 32);
        let (out_mid2, out_high) = self.split_low_high(high, 2 * BITS - 32, 32);
        let shift = self.constant(GoldilocksField::from_canonical_u32(1 << (32 - BITS)));
        let out_mid2_shifted = self.mul(shift, out_mid2);
        let out_mid = self.add(out_mid1, out_mid2_shifted);
        BigUintTarget {
            limbs: vec![out_low, out_mid, out_high],
        }
    }
}

fn conditional_zero<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    if_zero: Target,
    then_zero: Target,
) {
    let quot = builder.add_virtual_target();
    builder.add_simple_generator(ConditionalZeroGenerator {
        if_zero,
        then_zero,
        quot,
        _phantom: PhantomData::<F>,
    });
    let prod = builder.mul(if_zero, quot);
    builder.connect(prod, then_zero);
}

pub struct ConvolutionGate;

impl<F: RichField + Extendable<1>> SimpleGate<F> for ConvolutionGate {
    const ID: &'static str = "ConvolutionGate";
    const INPUTS_PER_OP: usize = 40;
    const OUTPUTS_PER_OP: usize = 40;
    const DEGREE: usize = 2;
    fn eval<const D: usize>(
        wires: &[<F as Extendable<D>>::Extension],
    ) -> Vec<<F as Extendable<D>>::Extension>
    where
        F: Extendable<D>,
    {
        let mut output = vec![<F as Extendable<D>>::Extension::ZERO; 40];
        for i in 0..20 {
            for j in 0..20 {
                output[i + j] += wires[i] * wires[j + 20];
            }
        }
        output
    }
}

//fn sub_no_borrow<F: RichField + Extendable<D> + Extendable<1>>

fn pad_to<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &[Target],
    size: usize,
) -> Vec<Target> {
    (0..size)
        .map(|i| a.get(i).copied().unwrap_or_else(|| builder.zero()))
        .collect()
}

fn add_no_carry<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &[Target],
    b: &[Target],
) -> Vec<Target> {
    let out_len = a.len().max(b.len());
    (0..out_len)
        .map(|i| {
            let ai = a.get(i).copied().unwrap_or_else(|| builder.zero());
            let bi = b.get(i).copied().unwrap_or_else(|| builder.zero());
            builder.add(ai, bi)
        })
        .collect()
}

fn sub_no_carry<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &[Target],
    b: &[Target],
) -> Vec<Target> {
    let out_len = a.len().max(b.len());
    (0..out_len)
        .map(|i| {
            let ai = a.get(i).copied().unwrap_or_else(|| builder.zero());
            let bi = b.get(i).copied().unwrap_or_else(|| builder.zero());
            builder.sub(ai, bi)
        })
        .collect()
}

fn mul_karatsuba_no_carry<F: RichField + Extendable<D> + Extendable<1>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &[Target],
    b: &[Target],
) -> Vec<Target> {
    let padded_len = a.len().max(b.len());
    if padded_len <= 20 {
        let mut inputs = a.to_vec();
        inputs.resize(20, builder.zero());
        inputs.extend_from_slice(b);
        inputs.resize(40, builder.zero());
        let mut output = ConvolutionGate::apply(builder, &inputs);
        output.resize_with(a.len() + b.len(), || unreachable!());
        output
    } else {
        let padded_a = pad_to(builder, a, padded_len);
        let padded_b = pad_to(builder, b, padded_len);
        let l = padded_len.div_ceil(2);
        let a_low = &padded_a[0..l];
        let a_high = &padded_a[l..];
        let b_low = &padded_b[0..l];
        let b_high = &padded_b[l..];
        let a_sum = add_no_carry(builder, a_low, a_high);
        let b_sum = add_no_carry(builder, b_low, b_high);
        let c0 = mul_karatsuba_no_carry(builder, a_low, b_low);
        let c2 = mul_karatsuba_no_carry(builder, a_high, b_high);
        let prod = mul_karatsuba_no_carry(builder, &a_sum, &b_sum);
        let diff1 = sub_no_carry(builder, &prod, &c0);
        let c1 = sub_no_carry(builder, &diff1, &c2);
        let mut output: Vec<_> = (0..2 * padded_len)
            .map(|i| if i < 2 * l { c0[i] } else { c2[i - 2 * l] })
            .collect();
        for (n, &x) in c1.iter().enumerate() {
            output[n + l] = builder.add(output[n + l], x);
        }
        output.resize_with(a.len() + b.len(), || unreachable!());
        output
    }
}

impl<F: RichField + Extendable<D> + Extendable<1>, const D: usize, const BITS: usize>
    CircuitBuilderBigUint<F, D, BITS> for CircuitBuilder<F, D>
{
    fn add_virtual_biguint_target(&mut self, n_limbs: usize) -> BigUintTarget<BITS> {
        let limbs = (0..n_limbs)
            .map(|_| {
                let t = self.add_virtual_target();
                self.range_check(t, BITS);
                t
            })
            .collect();
        BigUintTarget { limbs }
    }

    fn add_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let num_limbs = a.num_limbs().max(b.num_limbs());

        let zero = self.zero();
        let mut limbs: Vec<_> = (0..num_limbs)
            .map(|i| {
                let a_limb = a.limbs.get(i).copied().unwrap_or(zero);
                let b_limb = b.limbs.get(i).copied().unwrap_or(zero);
                self.add(a_limb, b_limb)
            })
            .collect();

        for i in 0..num_limbs - 1 {
            let [low, high] = limbs.get_many_mut([i, i + 1]).unwrap();
            carry_mut(self, low, high, BITS, BITS + 1);
        }
        BigUintTarget { limbs }
    }

    fn constant_biguint(&mut self, value: &BigUint) -> BigUintTarget<BITS> {
        let limb_values = split_biguint::<BITS>(value);
        let limbs = limb_values
            .into_iter()
            .map(|l| self.constant(F::from_canonical_u32(l)))
            .collect();
        BigUintTarget { limbs }
    }

    fn mul_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let mut limbs = mul_karatsuba_no_carry(self, &a.limbs, &b.limbs);
        for i in 0..limbs.len() - 1 {
            let [low, high] = limbs.get_many_mut([i, i + 1]).unwrap();
            carry_mut(self, low, high, BITS, 63);
        }
        BigUintTarget { limbs }
    }

    fn connect_biguint(&mut self, lhs: &BigUintTarget<BITS>, rhs: &BigUintTarget<BITS>) {
        let min_limbs = lhs.num_limbs().min(rhs.num_limbs());
        for i in 0..min_limbs {
            self.connect(lhs.limbs[i], rhs.limbs[i]);
        }

        for i in min_limbs..lhs.num_limbs() {
            self.assert_zero(lhs.limbs[i]);
        }
        for i in min_limbs..rhs.num_limbs() {
            self.assert_zero(rhs.limbs[i]);
        }
    }

    fn div_rem_biguint(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> (BigUintTarget<BITS>, BigUintTarget<BITS>) {
        let a_len = a.limbs.len();
        let b_len = b.limbs.len();
        let div_num_limbs = if b_len > a_len + 1 {
            0
        } else {
            a_len - b_len + 1
        };

        let div = self.add_virtual_biguint_target(div_num_limbs);
        let rem = self.add_virtual_biguint_target(b_len);

        self.add_simple_generator(BigUintDivRemGenerator::<F, D, BITS> {
            a: a.clone(),
            b: b.clone(),
            div: div.clone(),
            rem: rem.clone(),
            _phantom: PhantomData,
        });

        let div_b = self.mul_biguint(&div, b);
        let div_b_plus_rem = self.add_biguint(&div_b, &rem);
        self.connect_biguint(a, &div_b_plus_rem);

        let cmp_rem_b = self.le_biguint(b, &rem);
        self.assert_zero(cmp_rem_b.target);

        (div, rem)
    }

    fn le_biguint(&mut self, a: &BigUintTarget<BITS>, b: &BigUintTarget<BITS>) -> BoolTarget {
        let padded_len = a.num_limbs().max(b.num_limbs());
        let padded_a = pad_to(self, &a.limbs, padded_len);
        let padded_b = pad_to(self, &b.limbs, padded_len);
        list_le_circuit(self, padded_a, padded_b, BITS)
    }

    fn if_biguint(
        &mut self,
        condition: BoolTarget,
        then_t: &BigUintTarget<BITS>,
        else_t: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let l = then_t.num_limbs().max(else_t.num_limbs());
        let limbs = (0..l)
            .map(|i| {
                let t1 = then_t.limbs.get(i).copied().unwrap_or_else(|| self.zero());
                let t2 = else_t.limbs.get(i).copied().unwrap_or_else(|| self.zero());
                self._if(condition, t1, t2)
            })
            .collect();
        BigUintTarget { limbs }
    }
}

pub trait ReadBigUint<const BITS: usize> {
    fn read_target_biguint(&mut self) -> IoResult<BigUintTarget<BITS>>;
}

impl<const BITS: usize> ReadBigUint<BITS> for Buffer<'_> {
    fn read_target_biguint(&mut self) -> IoResult<BigUintTarget<BITS>> {
        let num_limbs = self.read_usize()?;
        let mut limbs = Vec::with_capacity(num_limbs);
        while limbs.len() < num_limbs {
            limbs.push(self.read_target()?);
        }
        Ok(BigUintTarget { limbs })
    }
}

pub trait WriteBigUint<const BITS: usize> {
    fn write_target_biguint(&mut self, x: &BigUintTarget<BITS>) -> IoResult<()>;
}

impl<W: Write, const BITS: usize> WriteBigUint<BITS> for W {
    fn write_target_biguint(&mut self, x: &BigUintTarget<BITS>) -> IoResult<()> {
        self.write_usize(x.num_limbs())?;
        for limb in &x.limbs {
            self.write_target(*limb)?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct BigUintDivRemGenerator<F: RichField + Extendable<D>, const D: usize, const BITS: usize> {
    a: BigUintTarget<BITS>,
    b: BigUintTarget<BITS>,
    div: BigUintTarget<BITS>,
    rem: BigUintTarget<BITS>,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, const BITS: usize> SimpleGenerator<F, D>
    for BigUintDivRemGenerator<F, D, BITS>
{
    fn id(&self) -> String {
        "BigUintDivRemGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.a.limbs.iter().chain(&self.b.limbs).copied().collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<(), anyhow::Error> {
        let a = witness.get_biguint_target(self.a.clone());
        let b = witness.get_biguint_target(self.b.clone());
        let (div, rem) = a.div_rem(&b);

        out_buffer.set_biguint_target(&self.div, &div)?;
        out_buffer.set_biguint_target(&self.rem, &rem)?;
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target_biguint(&self.a)?;
        dst.write_target_biguint(&self.b)?;
        dst.write_target_biguint(&self.div)?;
        dst.write_target_biguint(&self.rem)
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self {
            a: src.read_target_biguint()?,
            b: src.read_target_biguint()?,
            div: src.read_target_biguint()?,
            rem: src.read_target_biguint()?,
            _phantom: PhantomData,
        })
    }
}

pub trait GeneratedValuesBigUint<F: PrimeField, const BITS: usize> {
    fn set_biguint_target(
        &mut self,
        target: &BigUintTarget<BITS>,
        value: &BigUint,
    ) -> anyhow::Result<()>;
}

impl<F: PrimeField, const BITS: usize> GeneratedValuesBigUint<F, BITS> for GeneratedValues<F> {
    fn set_biguint_target(
        &mut self,
        target: &BigUintTarget<BITS>,
        value: &BigUint,
    ) -> anyhow::Result<()> {
        let limbs = split_biguint::<BITS>(value);
        assert!(target.num_limbs() >= limbs.len());
        for (i, &limb) in target.limbs.iter().enumerate() {
            self.set_target(
                limb,
                F::from_canonical_u32(limbs.get(i).copied().unwrap_or(0)),
            )?;
        }
        Ok(())
    }
}

pub trait WitnessBigUintBool<F: PrimeField64>: Witness<F> {
    fn set_bool_targets_from_biguint(
        &mut self,
        targets: &[BoolTarget],
        value: &BigUint,
    ) -> anyhow::Result<()> {
        if value.bits() > targets.len() as u64 {
            return Err(anyhow!("value does not fit in targets"));
        }
        for (i, &target) in targets.iter().enumerate() {
            self.set_bool_target(target, value.bit(i as u64))?;
        }
        Ok(())
    }
}

impl<T: Witness<F>, F: PrimeField64> WitnessBigUintBool<F> for T {}

pub trait WitnessBigUint<F: PrimeField64, const BITS: usize>: Witness<F> {
    fn get_biguint_target(&self, target: BigUintTarget<BITS>) -> BigUint;
    fn set_biguint_target(
        &mut self,
        target: &BigUintTarget<BITS>,
        value: &BigUint,
    ) -> Result<(), anyhow::Error>;
}

impl<T: Witness<F>, F: PrimeField64, const BITS: usize> WitnessBigUint<F, BITS> for T {
    fn get_biguint_target(&self, target: BigUintTarget<BITS>) -> BigUint {
        target
            .limbs
            .into_iter()
            .rev()
            .fold(BigUint::zero(), |acc, limb| {
                (acc << BITS) + self.get_target(limb).to_canonical_biguint()
            })
    }

    fn set_biguint_target(
        &mut self,
        target: &BigUintTarget<BITS>,
        value: &BigUint,
    ) -> Result<(), anyhow::Error> {
        let limb_values = split_biguint::<BITS>(value);
        assert!(target.num_limbs() >= limb_values.len());
        for (n, &t) in target.limbs.iter().enumerate() {
            self.set_target(
                t,
                F::from_canonical_u32(limb_values.get(n).copied().unwrap_or(0)),
            )?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct ConditionalZeroGenerator<F: RichField + Extendable<D>, const D: usize> {
    if_zero: Target,
    then_zero: Target,
    quot: Target,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for ConditionalZeroGenerator<F, D>
{
    fn id(&self) -> String {
        "ConditionalZeroGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        vec![self.if_zero, self.then_zero]
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> anyhow::Result<()> {
        let if_zero = witness.get_target(self.if_zero);
        let then_zero = witness.get_target(self.then_zero);
        if if_zero.is_zero() {
            out_buffer.set_target(self.quot, F::ZERO)?;
        } else {
            out_buffer.set_target(self.quot, then_zero / if_zero)?;
        }

        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target(self.if_zero)?;
        dst.write_target(self.then_zero)?;
        dst.write_target(self.quot)
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self {
            if_zero: src.read_target()?,
            then_zero: src.read_target()?,
            quot: src.read_target()?,
            _phantom: PhantomData,
        })
    }
}

#[cfg(test)]
mod test {
    use num::{BigUint, Integer};
    use num_bigint::RandomBits;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use rand::{Rng, rngs::OsRng};

    use super::{BigUintTarget, CircuitBuilderBigUint};

    type F = GoldilocksField;
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;

    #[test]
    fn test_multiplication() -> anyhow::Result<()> {
        let x = OsRng.sample(RandomBits::new(1024));
        let y = OsRng.sample(RandomBits::new(1024));
        let z = (&x) * (&y);
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let x_t: BigUintTarget<28> = builder.constant_biguint(&x);
        let y_t = builder.constant_biguint(&y);
        let z_t = builder.constant_biguint(&z);
        let prod_t = builder.mul_biguint(&x_t, &y_t);
        builder.connect_biguint(&prod_t, &z_t);
        let data = builder.build::<C>();
        let proof = data.prove(PartialWitness::new())?;
        data.verify(proof)
    }

    #[test]
    fn test_modulus() -> anyhow::Result<()> {
        let x: BigUint = OsRng.sample(RandomBits::new(8));
        let y = OsRng.sample(RandomBits::new(4));
        let (div, rem) = x.div_rem(&y);
        println!("{x} {y} {div} {rem}");
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let x_t: BigUintTarget<28> = builder.constant_biguint(&x);
        let y_t = builder.constant_biguint(&y);
        let div_t_1 = builder.constant_biguint(&div);
        let rem_t_1 = builder.constant_biguint(&rem);
        let (div_t_2, rem_t_2) = builder.div_rem_biguint(&x_t, &y_t);
        builder.connect_biguint(&div_t_1, &div_t_2);
        builder.connect_biguint(&rem_t_1, &rem_t_2);
        let data = builder.build::<C>();
        let proof = data.prove(PartialWitness::new())?;
        data.verify(proof)
    }
}
