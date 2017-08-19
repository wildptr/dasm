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
	AF = add_ex(a[3:0], b[3:0], cin)[4];
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

proc push32_segr(data:16)
{
	// NOTE: For some CPU models, upper 16 bits may be unchanged.
	call push32({0:16}.data);
}

proc pop32():32
{
	data = load 4, SP;
	return data;
}
