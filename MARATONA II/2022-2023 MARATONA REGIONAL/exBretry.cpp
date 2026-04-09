#include<bits/stdc++.h>
using namespace std;

long long memo[32][2][2][2][2][2][2];// bit

const int MOD = 1000000000 + 7;
long long L1, R1, L2, R2, L3, R3;
int mod_pow(long long a, long long e, int m) {
    long long res = 1;
    while (e > 0) {
        if (e & 1) res = res * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return res;
}
int inv(int a, int m) {
    return mod_pow(a, m - 2, m);
}

long long solve(int bit, int tightUp1, int tightDown1, int tightUp2, int tightDown2, int tightUp3, int tightDown3){

    if(bit < 0){
        return 1;
    }

    if(memo[bit][tightUp1][tightDown1][tightUp2][tightDown2][tightUp3][tightDown3] != -1){
        return memo[bit][tightUp1][tightDown1][tightUp2][tightDown2][tightUp3][tightDown3];
    }

    long long ans = 0;

    int limitUp1 = tightUp1 ?(R1 >> bit) & 1 : 1, limitDown1 = tightDown1 ? (L1 >> bit) & 1 : 0;
    int limitUp2 = tightUp2 ?(R2 >> bit) & 1 : 1, limitDown2 = tightDown2 ? (L2 >> bit) & 1 : 0;
    int limitUp3 = tightUp3 ?(R3 >> bit) & 1 : 1, limitDown3 = tightDown3 ? (L3 >> bit) & 1 : 0;

    for(int i = limitDown1; i<=limitUp1;i++){
        for(int j = limitDown2; j<=limitUp2;j++){

            int k = i^j;
            if((k > limitUp3) || (k < limitDown3)) continue;
            int newTightUp1 = (tightUp1 && (i == limitUp1)), newTightDown1 = (tightDown1 && (i == limitDown1)); 
            int newTightUp2 = (tightUp2 && (j == limitUp2)), newTightDown2 = (tightDown2 && (j == limitDown2));
            int newTightUp3 = (tightUp3 && (k == limitUp3)), newTightDown3 = (tightDown3 && (k == limitDown3));

            ans += solve(bit-1, newTightUp1, newTightDown1, newTightUp2, newTightDown2, newTightUp3, newTightDown3) % MOD;

        }
    }

    return memo[bit][tightUp1][tightDown1][tightUp2][tightDown2][tightUp3][tightDown3] = ans;
}


int main(){

    long long l1, l2, l3, r1, r2, r3;
    cin >> l1 >> r1 >> l2 >> r2 >> l3 >> r3;
    L1 = l1; L2 = l2; L3 =l3; R1 = r1; R2 =r2; R3 =r3;


    memset(memo, -1, sizeof(memo));
    long long total = ((R1 - L1 + 1) * (R2 - L2 + 1) % MOD) * (R3 - L3 + 1) % MOD;

    long long perde = solve(31, true, true, true, true, true, true);
    // cout << "perde, total: " << perde << total << endl;
    long long result = ((1 - ((perde * inv(total, MOD)) % MOD)) + MOD)%MOD;
    
    cout << result << endl;

    return 0;
}