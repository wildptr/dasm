let parity(x:8) =
  ~(x[7]^x[6]^x[5]^x[4]^x[3]^x[2]^x[1]^x[0])

let adc8(a:8, b:8, cin:1) =
  let sum1 = add_ex(a, b, cin) in
  let cout = sum1[8] in
  let sum = sum1[7:0] in
  CF = cout;
  OF = cout ^ sum[7] ^ a[7] ^ b[7];
  ZF = sum == '00000000';
  SF = sum[7];
  AF = add_ex(a[3:0], b[3:0], cin)[4];
  PF = parity(sum);
  sum
