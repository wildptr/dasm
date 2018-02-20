//template proc adc<N, S, C>(a:N, b:N):N
//{
//	let sum1 = add_with_carry(a, b^sign_extend(S,N), C^S);
//	let cout = sum1[N];
//	let out = sum1[N-1:0];
//	CF = cout^S;
//	PF = ~^out[7:0];
//	AF = a[4] ^ b[4] ^ out[4] ^ S;
//	ZF = out == {0:N};
//	SF = out[N-1];
//	OF = cout ^ out[N-1] ^ a[N-1] ^ b[N-1];
//	output out;
//}

template proc add<N>(a:N, b:N):N
{
	CF = add_with_carry(a, b, '0')[N];
	ZF = a+b == {0:N};
	SF = less(a+b, {0:N});
	OF = CF ^ SF ^ a[N-1] ^ b[N-1];
	output a+b;
}

template proc adc<N>(a:N, b:N):N
{
	//let out = a + b + zero_extend(CF, N);
	let out = a + b + {0:N-1}.CF;
	CF = add_with_carry(a, b, CF)[N];
	ZF = out == {0:N};
	SF = less(out, {0:N});
	OF = CF ^ SF ^ a[N-1] ^ b[N-1];
	output out;
}

template proc sub<N>(a:N, b:N):N
{
	CF = below(a, b);
	ZF = a-b == {0:N};
	SF = less(a-b, {0:N});
	OF = SF ^ less(a, b);
	output a-b;
}

template proc sbb<N>(a:N, b:N)
{
	//let out = a - b - zero_extend(CF, N);
	let out = a - b - {0:N-1}.CF;
	CF = ~add_with_carry(a, ~b, ~CF)[N];
	ZF = out == {0:N};
	SF = less(out, {0:N});
	OF = CF ^ SF ^ a[N-1] ^ b[N-1];
}

template proc log_op<N, OP>(a:N, b:N):N
{
	let out = OP(a, b);
	CF = '0';
	//PF = ~^out[7:0];
	//AF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = '0';
	output out;
}

template proc shl<N, M>(x:N, n:M):N
{
	let out = shift_left(x, n);
	// TODO: the following is incorrect; see 325383.pdf p.1236
	//PF = ~^out[7:0];
	//AF = undefined(1);
	CF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = undefined(1);
	output out;
}

template proc shr<N, M>(x:N, n:M):N
{
	let out = log_shift_right(x, n);
	//PF = ~^out[7:0];
	//AF = undefined(1);
	CF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = undefined(1);
	output out;
}

template proc sar<N, M>(x:N, n:M):N
{
	let out = ari_shift_right(x, n);
	CF = undefined(1);
	//PF = ~^out[7:0];
	//AF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = undefined(1);
	output out;
}

proc add8  = add< 8>;
proc add16 = add<16>;
proc add32 = add<32>;

proc adc8  = adc< 8>;
proc adc16 = adc<16>;
proc adc32 = adc<32>;

proc sub8  = sub< 8>;
proc sub16 = sub<16>;
proc sub32 = sub<32>;

proc sbb8  = sbb< 8>;
proc sbb16 = sbb<16>;
proc sbb32 = sbb<32>;

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
	ESP = ESP - {4:32};
	store 4, ESP, data;
}

proc pop32():32
{
	output load(4, ESP);
	ESP = ESP + {4:32};
}

proc push_segr32(data:16)
{
	// NOTE: For some CPU models, upper 16 bits may be unchanged.
	call push32({0:16}.data);
}

template proc inc<N>(in:N)
{
	let out = in + {1:N};
	//PF = ~^out[7:0];
	//AF = in[4] ^ out[4];
	ZF = out == {0:N};
	SF = out[N-1];
	//OF = sum1[N] ^ out[N-1] ^ in[N-1];
	OF = undefined(1);
}

template proc dec<N>(in:N)
{
	let out = in - {1:N};
	ZF = out == {0:N};
	SF = out[N-1];
	OF = undefined(1);
}

proc inc8  = inc< 8>;
proc inc16 = inc<16>;
proc inc32 = inc<32>;

proc dec8  = dec< 8>;
proc dec16 = dec<16>;
proc dec32 = dec<32>;
