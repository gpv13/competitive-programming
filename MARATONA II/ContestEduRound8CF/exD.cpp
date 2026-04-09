#include<bits/stdc++.h>
using namespace std;

//memo[bit][upperTight][lowerTight][mod]
long long memo[2002][2][2][2002];
string L, M;
int D;
int modul;
#define MOD 1000000007
long long solve(int bit, int upperTight, int lowerTight, int mod){

    if(memo[bit][upperTight][lowerTight][mod] != -1){
        return memo[bit][upperTight][lowerTight][mod];
    }
    if(bit == M.size()){
        return mod == 0;
    }
    long long ans = 0;
    int upperLimit = upperTight ? (M[bit] - '0') : 9;
    int lowerLimit = lowerTight ? (L[bit] - '0') : 0;
    // if((bit%2)){
    //     upperLimit = D; lowerLimit = D;
    // }
    for(int i=lowerLimit;i<=upperLimit;i++){
        if(!(bit%2) && i == D) continue;
        if(bit%2 && i != D) continue;
        int newUpperTight = upperTight && (i == (M[bit]-'0'));
        int newLowerTight = lowerTight && (i == (L[bit]-'0'));
        ans+=solve(bit+1, newUpperTight, newLowerTight, (mod*10 + i)%modul)%MOD;
    }



    return memo[bit][upperTight][lowerTight][mod] = ans % MOD;

}

int main(){

    int m, d;
    cin >> m >> d;
    string a, b;
    cin >> a >> b;
    L = a; M = b; modul = m; D = d;
    memset(memo, -1, sizeof(memo));
    long long ans = solve(0, true, true, 0)%MOD;

    cout << ans << endl; 

    return 0;
}