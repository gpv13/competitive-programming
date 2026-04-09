#include<bits/stdc++.h>
using namespace std;
 
long long int mod = 998244353ll;
 
// long long int lcm(long long int m, long long int n){
//     return ((m*n)/__gcd(m,n));
// }
 
int main(){
    int n;
    cin >> n;
    // long long int ans = 1;
    vector<bool> tem(100001, false);
    for(int i = 0;  i < n; i++){
        long long int a,b;
        cin >> a >> b;
        long long int r = b/__gcd(a,b);
        // long long int prod = 1;
        if(r != 1){
            for(long long int j = 2; j*j <= r; j++){
                if(r%j == 0)
                    tem[j] = true;                
                    // prod *= j;

                while(r%j ==0)
                    r/=j;
            }
            if(r>1)tem[r] = true;
            // prod *= r;
        }
        // ans%=mod;
        // ans = lcm(ans, prod);
    }
    long long ans = 1;
    bool mudou = false;
    for(int i=2;i<tem.size();i++){
        if(tem[i]) {ans *= i; mudou = true;}
        ans %= mod;
        
    }

    if(!mudou)
        ans = 2;
    cout << ans%mod << endl;
    return 0;
}