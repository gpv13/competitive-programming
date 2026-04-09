#include<bits/stdc++.h>
using namespace std;

const int MAX = 2*5e3 + 10;

long long fat[MAX];
long long invfat[MAX];

long long inv(long long a, long long b) {
	return a > 1 ? b - inv(b%a, a)*b/a : 1;
}

void buildFat(long long mod){
    fat[0] = invfat[0] = 1;
    for(int i = 1; i<MAX;i++){
        fat[i] = i*fat[i-1] %mod;
        invfat[i] = inv(fat[i], mod);
    }
}

long long choose(int big, int smal, long long mod){
    if(big < smal || smal < 0) return 0;
    return (fat[big] * invfat[smal] %mod) * invfat[big-smal] % mod;
}

int main(){

    int n;
    cin >> n;
    long long mod;
    cin >> mod;
    
    buildFat(mod);

    long long ans = 0;

    for(int i = 0; i<=n/2;i++){
        long long soma = choose(n, 2*i, mod) * choose(2*i, i, mod) % mod;
        
        for(int j=0;j<=n/2;j++){
            int over = 2*j - (n - 2*i);
            ans += soma * choose(2*i, over, mod) % mod * choose(2*j, j, mod) % mod;
        }
    }
    cout << ans % mod << endl;


    return 0;
}