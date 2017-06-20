proc parity(x:8):1
{
	return ~(x[7]^x[6]^x[5]^x[4]^x[3]^x[2]^x[1]^x[0]);
}

proc adjust_flag(a:4, b:4):1
{
	let sum1 = '0' a + '0' b;
	return sum1[4];
}

proc adc8(a:8, b:8, cin:1):8
{
	let sum1 = '0' a + '0' b + '0000000' cin;
	let sum = sum1[7:0];
	CF = sum1[8];
	OF = sum1[8] ^ sum1[7] ^ a[7] ^ b[7];
	ZF = sum == '00000000';
	SF = sum[8];
	AF = adjust_flag(a[3:0], b[3:0]);
	PF = parity(sum);
	return sum;
}
