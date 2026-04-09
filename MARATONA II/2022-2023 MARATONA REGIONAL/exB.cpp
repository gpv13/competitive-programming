#include<bits/stdc++.h>
using namespace std;
//memo[bit][tight1][tight2][tight3]
long long int memo[30][2][2][2] = {-1};

#define MOD 1000000007

long long int solve(long long int bit, long long int tight1, long long int tight2, long long int tight3, long long int k1, long long int k2, long long int k3){

    if(bit<0) return 1;
    if(memo[bit][tight1][tight2][tight3] != -1){
        return memo[bit][tight1][tight2][tight3];
    }
    long long int ans = 0;
    long long int limit1 = tight1 ? (k1 >> bit) & 1 : 1;
    long long int limit2 = tight2 ? (k2 >> bit) & 1 : 1;
    long long int limit3 = tight3 ? (k3 >> bit) & 1 : 1;




    for(long long int i=0;i<=limit1;i++){
        for(long long int j=0;j<=limit2;j++){

            long long int b3 = i^j;
            if(b3 <=limit3){

                long long int newTight1 = tight1 && (i==limit1);
                long long int newTight2 = tight2 && (j==limit2);
                long long int newTight3 = tight3 && (b3==limit3); 
                ans += solve(bit-1, newTight1, newTight2, newTight3, k1, k2, k3);

            }

        }
    }

    return memo[bit][tight1][tight2][tight3] = ans;

}

long long int count_xor_zero(long long int k1, long long int k2, long long int k3){
    memset(memo, -1, sizeof(memo));
    return solve(29, true, true, true, k1, k2, k3)%MOD;
}

long long power(long long base, long long exp) {
    long long res = 1;
    base %= 1000000007;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % 1000000007;
        base = (base * base) % 1000000007;
        exp /= 2;
    }
    return res;
}

long long modInverse(long long n) {
    return power(n, 1000000007 - 2);
}

int main(){

    long long int l1, r1, l2, r2, l3, r3;
    cin >> l1 >> r1 >> l2 >> r2 >> l3 >> r3;
    
    long long contaXorZero = 0;

    contaXorZero = count_xor_zero(r1, r2, r3) - count_xor_zero(l1-1, r2, r3) - count_xor_zero(r1, l2-1, r3) - count_xor_zero(r1, r2, l3-1) + count_xor_zero(l1-1, l2-1, r3) + count_xor_zero(l1-1, r2, l3-1) + count_xor_zero(r1, l2-1,l3-1) - count_xor_zero(l1-1, l2-1, l3-1);
    long long contaTotal = (((r1 - l1 + 1)%MOD * (r2 - l2 + 1)%MOD)%MOD * (r3 - l3 + 1)%MOD)%MOD;

    long long int perde = (contaXorZero * modInverse(contaTotal)) % MOD;
    cout << (1 - perde + MOD) % MOD << endl; 


    return 0;
}