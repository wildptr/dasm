template proc adc<N, S, C>(a:N, b:N):N
{
	let sum1 = add_ex(a, b, C^S);
	let cout = sum1[N];
	let out = sum1[N-1:0];
	CF = cout^S;
	PF = ~^out[7:0];
	AF = a[4] ^ b[4] ^ out[4] ^ S;
	ZF = out == {0:N};
	SF = out[N-1];
	OF = cout ^ out[N-1] ^ a[N-1] ^ b[N-1];
	return out;
}

template proc log_op<N, OP>(a:N, b:N):N
{
	let out = OP(a, b);
	CF = '0';
	PF = ~^out[7:0];
	AF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = '0';
	return out;
}

template proc shl<N, M>(x:N, n:M):N
{
	let out1 = shift_left(CF.x, n);
	let out = out1[N-1:0];
	CF = out1[N];
	// TODO: the following is incorrect; see 325383.pdf p.1236
	PF = ~^out[7:0];
	AF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = undefined(1);
	return out;
}

template proc shr<N, M>(x:N, n:M):N
{
	let out1 = log_shift_right(x.CF, n);
	let out = out1[N:1];
	CF = out[0];
	PF = ~^out[7:0];
	AF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = undefined(1);
	return out;
}

template proc sar<N, M>(x:N, n:M):N
{
	let out1 = ari_shift_right(x.CF, n);
	let out = out1[N:1];
	CF = out[0];
	PF = ~^out[7:0];
	AF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = undefined(1);
	return out;
}

proc add8  = adc< 8, '0', '0'>;
proc add16 = adc<16, '0', '0'>;
proc add32 = adc<32, '0', '0'>;

proc adc8  = adc< 8, '0', CF>;
proc adc16 = adc<16, '0', CF>;
proc adc32 = adc<32, '0', CF>;

proc sub8  = adc< 8, '1', '0'>;
proc sub16 = adc<16, '1', '0'>;
proc sub32 = adc<32, '1', '0'>;

proc sbb8  = adc< 8, '1', CF>;
proc sbb16 = adc<16, '1', CF>;
proc sbb32 = adc<32, '1', CF>;

proc or8  = log_op< 8, or>;
proc or16 = log_op<16, or>;
proc or32 = log_op<32, or>;

proc and8  = log_op< 8, and>;
proc and16 = log_op<16, and>;
proc and32 = log_op<32, and>;

proc xor8  = log_op< 8, xor>;
proc xor16 = log_op<16, xor>;
proc xor32 = log_op<32, xor>;

proc shl8  = shl< 8, 5>;
proc shl16 = shl<16, 5>;
proc shl32 = shl<32, 5>;

proc shr8  = shr< 8, 5>;
proc shr16 = shr<16, 5>;
proc shr32 = shr<32, 5>;

proc sar8  = sar< 8, 5>;
proc sar16 = sar<16, 5>;
proc sar32 = sar<32, 5>;

proc push32(data:32)
{
	SP = SP - {4:32};
	store 4, SP, data;
}

proc pop32():32
{
	let data = load(4, SP);
	SP = SP + {4:32};
	return data;
}

proc push_segr32(data:16)
{
	// NOTE: For some CPU models, upper 16 bits may be unchanged.
	call push32({0:16}.data);
}

template proc inc_dec<N, S>(in:N)
{
	let sum1 = add_ex(in, repeat(S, N), ~S);
	let out = sum1[N-1:0];
	PF = ~^out[7:0];
	AF = in[4] ^ out[4];
	ZF = out == {0:N};
	SF = out[N-1];
	OF = sum1[N] ^ out[N-1] ^ in[N-1];
}

proc inc8  = inc_dec< 8, '0'>;
proc inc16 = inc_dec<16, '0'>;
proc inc32 = inc_dec<32, '0'>;

proc dec8  = inc_dec< 8, '1'>;
proc dec16 = inc_dec<16, '1'>;
proc dec32 = inc_dec<32, '1'>;

proc call32(pc:32, offset:32)
{
	call push32(pc);
	jump pc + offset;
}

proc ret32()
{
	let addr = call pop32();
	jump addr;
}

proc retn32(n:32)
{
	let addr = call pop32();
	SP = SP + n;
	jump addr;
}
