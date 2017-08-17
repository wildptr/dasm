proc parity(x:8):1
{
	return ~(x[7]^x[6]^x[5]^x[4]^x[3]^x[2]^x[1]^x[0]);
}

proc adc8(a:8, b:8, cin:1):8
{
	sum1 = add_ex(a, b, cin);
	cout = sum1[8];
	sum = sum1[7:0];
	CF = cout;
	PF = call parity(sum);
	AF = add_ex(a[3:0], b[3:0], cin)[4];
	ZF = sum == '00000000';
	SF = sum[7];
	OF = cout ^ sum[7] ^ a[7] ^ b[7];
	return sum;
}
