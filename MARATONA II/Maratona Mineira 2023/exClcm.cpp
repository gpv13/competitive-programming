#include<bits/stdc++.h>
using namespace std;

long long int mod = 998244353;

long long int lcm(long long int m, long long int n){
    return ((m*n)/__gcd(m,n))%mod;
}

int main(){
    int n;
    cin >> n;
    long long int ans = 1;
    bool mudou = false;
    for(int i = 0;  i < n; i++){
        long long int a,b;
        cin >> a >> b;
        long long int r = b/__gcd(a,b);
        long long int prod = 1;
        if(r != 1){
            for(long long int i = 2; i*i <= r; i++){
                if(r%i == 0){
                    prod *= i;
                    mudou = true;
                }
                while(r%i ==0)
                    r/=i;
            }
            if(r>1){
                prod *= r;
                mudou = true;
            }
        }
        ans = lcm(ans, prod);
    }
    if(!mudou)
        ans = 2;
    cout << ans << endl;
    return 0;
}