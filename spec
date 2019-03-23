template proc add<N>(a:N, b:N) -> out:N
{
	CF = carry(a, b, false);
	ZF = a+b == #0:N;
	SF = less(a+b, #0:N);
	OF = CF ^ SF ^ less(a, #0:N) ^ less(b, #0:N);
	out = a+b;
}

template proc adc<N>(a:N, b:N) -> out:N
{
	out = a + b + ite(CF, #1:N, #0:N);
	CF = carry(a, b, CF);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = CF ^ SF ^ less(a, #0:N) ^ less(b, #0:N);
}

template proc sub<N>(a:N, b:N) -> out:N
{
	CF = below(a, b);
	ZF = a == b;
	SF = less(a-b, #0:N);
	OF = SF ^ less(a, b);
	out = a-b;
}

template proc sbb<N>(a:N, b:N) -> out:N
{
	out = a - b - ite(CF, #1:N, #0:N);
	CF = ~carry(a, ~b, ~CF);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = ~CF ^ SF ^ less(a, #0:N) ^ less(b, #0:N);
}

template proc log_op<N, OP>(a:N, b:N) -> out:N
{
	out = OP(a, b);
	CF = false;
	//PF = ~^out[7:0];
	//AF = undefined(bool);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = false;
}

template proc shl_<N, M>(x:N, n:M) -> out:N
{
	out = shl(x, (n:N));
	// TODO: the following is incorrect; see 325383.pdf p.1236
	//PF = ~^out[7:0];
	//AF = undefined(bool);
	CF = undefined(bool);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = undefined(bool);
}

template proc shr<N, M>(x:N, n:M) -> out:N
{
	out = lshr(x, (n:N));
	//PF = ~^out[7:0];
	//AF = undefined(bool);
	CF = undefined(bool);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = undefined(bool);
}

template proc sar<N, M>(x:N, n:M) -> out:N
{
	out = ashr(x, (n:N));
	CF = undefined(bool);
	//PF = ~^out[7:0];
	//AF = undefined(bool);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = undefined(bool);
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

proc shl8  = shl_< 8, 5>;
proc shl16 = shl_<16, 5>;
proc shl32 = shl_<32, 5>;

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

proc pop32() -> out:32
{
	out = [SS:ESP]:32;
	ESP = ESP + #4:32;
}

proc push_segr32(data:16)
{
	// NOTE: For some CPU models, upper 16 bits may be unchanged.
	push32(#0:16.data);
}

template proc inc<N>(in:N) -> out:N
{
	out = in + #1:N;
	//PF = ~^out[7:0];
	//AF = in[4] ^ out[4];
	ZF = out == #0:N;
	SF = less(out, #0:N);
	//OF = sum1[N] ^ out[N-1] ^ in[N-1];
	OF = undefined(bool);
}

template proc dec<N>(in:N) -> out:N
{
	out = in - #1:N;
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = undefined(bool);
}

proc inc8  = inc< 8>;
proc inc16 = inc<16>;
proc inc32 = inc<32>;

proc dec8  = dec< 8>;
proc dec16 = dec<16>;
proc dec32 = dec<32>;

template proc neg<N>(in:N) -> out:N
{
	CF = below(#0:N, in);
	ZF = #0:N == in;
	SF = less(-in, #0:N);
	OF = SF ^ less(#0:N, in);
	out = -in;
}

proc neg8  = neg< 8>;
proc neg16 = neg<16>;
proc neg32 = neg<32>;

template proc not<N>(in:N) -> out:N
{
	out = ~in;
	CF = false;
	//PF = ~^out[7:0];
	//AF = undefined(bool);
	ZF = out == #0:N;
	SF = less(out, #0:N);
	OF = false;
}

proc not8  = not< 8>;
proc not16 = not<16>;
proc not32 = not<32>;

proc call32(dst:32)
{
	push32(pc);
	jump dst;
}

proc ret32()
{
	jump pop32();
}

proc retn32(n:16)
{
	var ra:32;
	ra = pop32();
	ESP = ESP + (n:32);
	jump ra;
}

proc leave32()
{
	ESP = EBP;
	EBP = pop32();
}

template proc mul<N>(a:N, b:N) -> out:(N+N)
{
	var prod:N+N;
	var overflow:bool;
	prod = (a:(N+N)) * (b:(N+N));
	overflow = (a*b:(N+N)) != prod;
	SF = undefined(bool);
	ZF = undefined(bool);
	CF = overflow;
	OF = overflow;
	out = prod;
}

template proc imul<N>(a:N, b:N) -> out:(N+N)
{
	var prod:N+N;
	var overflow:bool;
	prod = sign_extend(a, N+N) * sign_extend(b, N+N);
	overflow = sign_extend(a*b, N+N) != prod;
	SF = undefined(bool);
	ZF = undefined(bool);
	CF = overflow;
	OF = overflow;
	out = prod;
}

proc mul8  = mul<8>;
proc mul16 = mul<16>;
proc mul32 = mul<32>;

proc imul8  = imul<8>;
proc imul16 = imul<16>;
proc imul32 = imul<32>;

proc mulb(a:8)
{
	AX = mul8(AL, a);
}

proc mulw16(a:16)
{
	var tmp:32;
	tmp = mul16(AX, a);
	AX = extract(tmp,  0, 16);
	DX = extract(tmp, 16, 32);
}

proc mulw32(a:32)
{
	var tmp:64;
	tmp = mul32(EAX, a);
	EAX = extract(tmp,  0, 32);
	EDX = extract(tmp, 32, 64);
}

proc imulb(a:8)
{
	AX = imul8(AL, a);
}

proc imulw16(a:16)
{
	var tmp:32;
	tmp = imul16(AX, a);
	AX = extract(tmp,  0, 16);
	DX = extract(tmp, 16, 32);
}

proc imulw32(a:32)
{
	var tmp:64;
	tmp = imul32(EAX, a);
	EAX = extract(tmp,  0, 32);
	EDX = extract(tmp, 32, 64);
}
