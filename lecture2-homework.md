# 第2课 课后作业

## 第1题 转换为bit位 Num2Bits
![Num2Bits](https://github.com/punish-yh/zkcourse-homework/assets/59658062/3920f9cb-f7e6-4ea5-9066-24184cd23462)


## 第2题 判零 IsZero
![IsZero](https://github.com/punish-yh/zkcourse-homework/assets/59658062/d4a665be-6270-418b-8d70-16c63cae2f54)


## 第3题 相等 IsEqual
![IsEqual](https://github.com/punish-yh/zkcourse-homework/assets/59658062/54884825-3bbb-4a32-b71a-9c5d3e935187)


## 第4题 选择器 Selector
````
pragma circom 2.1.4;

// 判断两数是否相等
template IsEqual () {
    signal input in[2];
    signal output out;
    signal inv;

    inv <-- (in[0] - in[1]) == 0 ? 0 : 1 / (in[0] - in[1]);
    out <== - inv * (in[0] - in[1]) + 1;
    out * (in[0] - in[1]) === 0;
}

// 累加，计算 n 个数的和
template Sum (n) {
    signal input in[n];
    signal output out;
    signal sum[n + 1];

    sum[0] <== 0;
    for (var i = 0; i < n; i++) {
        sum[i + 1] <== in[i] + sum[i];
    }
    out <== sum[n];
}

template Selector (nChoices) {
    signal input in[nChoices];
    signal input index;
    signal output out;
    
    component iseq[nChoices];
    component sum = Sum(nChoices);
    for (var i = 0; i < nChoices; i++) {
        // 判断 i 与 index 是否相等
        iseq[i] = IsEqual();
        iseq[i].in[0] <== i;
        iseq[i].in[1] <== index;

        // 如果 i == index，累加 1 * in[i]
        // 如果 i != index，累加 0 * in[i]
        sum.in[i] <== iseq[i].out * in[i]; 
    }

    // 如果 index 不在索引范围内，则每个iseq[i].out = 0，因此 sum.out = 0
    out <== sum.out;
}

component main = Selector(5);

/* INPUT = {
    "in": ["9", "13", "21", "35", "5"],
    "index": "2"
} */
````


## 第5题 判负 IsNegative
````
pragma circom 2.1.4;

template Num2Bits(n) {
    signal input in;
    signal output out[n];
    var lc1=0;

    var e2=1;
    for (var i = 0; i<n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }

    lc1 === in;
}


// Returns 1 if in (in binary) > ct
template CompConstant(ct) {
    signal input in[254];
    signal output out;

    signal parts[127];
    signal sout;

    var clsb;
    var cmsb;
    var slsb;
    var smsb;

    var sum=0;

    var b = (1 << 128) -1;
    var a = 1;
    var e = 1;
    var i;

    for (i=0;i<127; i++) {
        clsb = (ct >> (i*2)) & 1;
        cmsb = (ct >> (i*2+1)) & 1;
        slsb = in[i*2];
        smsb = in[i*2+1];

        if ((cmsb==0)&&(clsb==0)) {
            parts[i] <== -b*smsb*slsb + b*smsb + b*slsb;
        } else if ((cmsb==0)&&(clsb==1)) {
            parts[i] <== a*smsb*slsb - a*slsb + b*smsb - a*smsb + a;
        } else if ((cmsb==1)&&(clsb==0)) {
            parts[i] <== b*smsb*slsb - a*smsb + a;
        } else {
            parts[i] <== -a*smsb*slsb + a;
        }

        sum = sum + parts[i];

        b = b -e;
        a = a +e;
        e = e*2;
    }

    sout <== sum;

    component num2bits = Num2Bits(135);

    num2bits.in <== sout;

    out <== num2bits.out[127];
}


template IsNegative() {
    signal input in;
    signal output out;

    var p = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    // (p - 1) \ 2 = 10944121435919637611123202872628637544274182200208017171849102093287904247808
    component num2bits = Num2Bits(254);
    component compconstant = CompConstant((p - 1) \ 2);
    num2bits.in <== in;
    compconstant.in <== num2bits.out; 
    out <== compconstant.out;

}

component main = IsNegative(); 

/* INPUT = {
    "in": "21888242871839275222246405745257275088548364400416034343698204186575808495616"
} */
````


## 第6题 少于 LessThan
````
pragma circom 2.1.4;

// 将 in 转换为 n 位二进制表达
template Num2Bits(n) {
    signal input in;
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <-- (in \ 2**i) % 2;
    }

    var accm = 0;
    for (var i = 0; i < n; i++) {
        accm += out[i] * 2**i;
    }
    accm === in;

    // 约束输出的每一位是 0 / 1
    for (var i = 0; i < n; i++) {
        out[i] * (1 - out[i]) === 0;
    }
}


// in[0] < in[1] 返回 1，否则返回0
template LessThan (n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);
    n2b.in <== in[1] - in[0] + (2**n); // n+1位二进制，最大数是 2**n
    out <== n2b.out[n];
}

component main = LessThan(3);

/* INPUT = {
    "in": ["3", "4"]
} */
````


## 第7题 整数除法 IntegerDivide
````
pragma circom 2.1.4;

// 将 in 转换为 n 位二进制表达
template Num2Bits(n) {
    signal input in;
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <-- (in \ 2**i) % 2;
    }

    var accm = 0;
    for (var i = 0; i < n; i++) {
        accm += out[i] * 2**i;
    }
    accm === in;

    // 约束输出的每一位是 0 / 1
    for (var i = 0; i < n; i++) {
        out[i] * (1 - out[i]) === 0;
    }
}

// in[0] < in[1] 返回 1，否则返回0
template LessThan (n) {
    // 先确定输入信号最多为 2**252 - 1
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);
    n2b.in <== in[0] - in[1] + (2**n); // n+1位二进制，最大数是 2**n
    out <== 1 - n2b.out[n];
}


// 限制 in 最多为 nbits 位
template Range(nbits) {
    signal input in;
    signal bits[nbits];
    var bitsum = 0;
    for (var i = 0; i < nbits; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
        bitsum = bitsum + 2 ** i * bits[i];
    }

    in === bitsum;
}

template IntegerDivide (nbits) {
    assert(nbits <= 126);
    signal input dividend;
    signal input divisor;

    signal output remainder;
    signal output quotient;
    
    // 限制被除数、除数最多为 nbits 位
    component range1 = Range(nbits);
    range1.in <== dividend;
    component range2 = Range(nbits);
    range2.in <== divisor;

    // 限制除数不能为0
    signal inv;
    inv <-- 1 / divisor;
    inv * divisor === 1;

    // 计算商和余数
    quotient <-- dividend \ divisor;
    remainder <== dividend - quotient * divisor;

    // 约束余数在范围 [0, divisor) 之间
    component lessthan = LessThan(nbits);
    lessthan.in[0] <== remainder;
    lessthan.in[1] <== divisor;
    lessthan.out === 1;

    // 约束是正确的计算
    dividend === quotient * divisor + remainder;
}

component main = IntegerDivide(9);

/* INPUT = {
    "dividend": "89",
    "divisor": "43"
} */
````
