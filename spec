proc parity(x:8):1
{
	return ~(x[7]^x[6]^x[5]^x[4]^x[3]^x[2]^x[1]^x[0]);
}

template proc adc<N, S>(a:N, b:N, cin:1):N
{
	sum1 = add_ex(a, b, cin^S);
	cout = sum1[N];
	out = sum1[N-1:0];
	CF = cout^S;
	PF = call parity(out[7:0]);
	AF = a[4] ^ b[4] ^ out[4] ^ S;
	ZF = out == {0:N};
	SF = out[N-1];
	OF = cout ^ out[N-1] ^ a[N-1] ^ b[N-1];
	return out;
}

template proc log_op<N, OP>(a:N, b:N):N
{
	out = OP(a, b);
	CF = '0';
	PF = call parity(out[7:0]);
	AF = undefined(1);
	ZF = out == {0:N};
	SF = out[N-1];
	OF = '0';
	return out;
}

proc adc8  = adc< 8, '0'>;
proc adc16 = adc<16, '0'>;
proc adc32 = adc<32, '0'>;

proc sbb8  = adc< 8, '1'>;
proc sbb16 = adc<16, '1'>;
proc sbb32 = adc<32, '1'>;

proc or8  = log_op< 8, or>;
proc or16 = log_op<16, or>;
proc or32 = log_op<32, or>;

proc and8  = log_op< 8, and>;
proc and16 = log_op<16, and>;
proc and32 = log_op<32, and>;

proc xor8  = log_op< 8, xor>;
proc xor16 = log_op<16, xor>;
proc xor32 = log_op<32, xor>;

proc push32(data:32)
{
	SP = SP - {4:32};
	store 4, SP, data;
}

proc pop32():32
{
	data = load 4, SP;
	SP = SP + {4:32};
	return data;
}

proc push32_segr(data:16)
{
	// NOTE: For some CPU models, upper 16 bits may be unchanged.
	call push32({0:16}.data);
}

template proc inc_dec<N, S>(in:N)
{
	sum1 = add_ex(in, repeat(S, N), ~S);
	out = sum1[N-1:0];
	PF = call parity(out[7:0]);
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
	addr = call pop32();
	jump addr;
}
