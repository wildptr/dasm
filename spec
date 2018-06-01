template proc add<N>(a:N, b:N):N
{
	CF = carry(a, b, '0');
	ZF = a+b == #0:N;
	SF = less(a+b, #0:N);
	OF = CF ^ SF ^ a[N-1] ^ b[N-1];
	return a+b;
}

template proc adc<N>(a:N, b:N):N
{
	var out:N;
	out = a + b + (CF:N);
	CF = carry(a, b, CF);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = CF ^ SF ^ a[N-1] ^ b[N-1];
	return out;
}

template proc sub<N>(a:N, b:N):N
{
	CF = below(a, b);
	ZF = a == b;
	SF = less(a-b, #0:N);
	OF = SF ^ less(a, b);
	return a-b;
}

template proc sbb<N>(a:N, b:N)
{
	var out:N;
	out = a - b - (CF:N);
	CF = ~carry(a, ~b, ~CF);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = CF ^ SF ^ a[N-1] ^ b[N-1];
}

template proc log_op<N, OP>(a:N, b:N):N
{
	var out:N;
	out = OP(a, b);
	CF = '0';
	//PF = ~^out[7:0];
	//AF = undefined(1);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = '0';
	return out;
}

template proc shl<N, M>(x:N, n:M):N
{
	var out:N;
	out = shift_left(x, n);
	// TODO: the following is incorrect; see 325383.pdf p.1236
	//PF = ~^out[7:0];
	//AF = undefined(1);
	CF = undefined(1);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = undefined(1);
	return out;
}

template proc shr<N, M>(x:N, n:M):N
{
	var out:N;
	out = log_shift_right(x, n);
	//PF = ~^out[7:0];
	//AF = undefined(1);
	CF = undefined(1);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = undefined(1);
	return out;
}

template proc sar<N, M>(x:N, n:M):N
{
	var out:N;
	out = ari_shift_right(x, n);
	CF = undefined(1);
	//PF = ~^out[7:0];
	//AF = undefined(1);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = undefined(1);
	return out;
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
	ESP = ESP - #4:32;
	[SS:ESP]:32 = data;
}

proc pop32():32
{
	var tmp:32;
	tmp = [SS:ESP]:32;
	ESP = ESP + #4:32;
	return tmp;
}

proc push_segr32(data:16)
{
	// NOTE: For some CPU models, upper 16 bits may be unchanged.
	push32(#0:16.data);
}

template proc inc<N>(in:N)
{
	var out:N;
	out = in + #1:N;
	//PF = ~^out[7:0];
	//AF = in[4] ^ out[4];
	ZF = out == #0:N;
	SF = less(out, #0:N);
	//OF = sum1[N] ^ out[N-1] ^ in[N-1];
	OF = undefined(1);
}

template proc dec<N>(in:N)
{
	var out:N;
	out = in - #1:N;
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = undefined(1);
}

proc inc8  = inc< 8>;
proc inc16 = inc<16>;
proc inc32 = inc<32>;

proc dec8  = dec< 8>;
proc dec16 = dec<16>;
proc dec32 = dec<32>;

template proc neg<N>(in:N):N
{
	CF = below(#0:N, in);
	ZF = #0:N == in;
	SF = less(-in, #0:N);
	OF = SF ^ less(#0:N, in);
	return -in;
}

proc neg8  = neg< 8>;
proc neg16 = neg<16>;
proc neg32 = neg<32>;

template proc not<N>(in:N):N
{
	var out:N;
	out = ~in;
	CF = '0';
	//PF = ~^out[7:0];
	//AF = undefined(1);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = '0';
	return out;
}

proc not8  = not< 8>;
proc not16 = not<16>;
proc not32 = not<32>;
