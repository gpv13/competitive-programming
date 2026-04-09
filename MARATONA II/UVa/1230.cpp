#include<bits/stdc++.h>
using namespace std;

long long binpow(long long a, long long b, long long m) {
    a %= m;
    long long res = 1;
    while (b > 0) {
        if (b & 1)
            res = res * a % m;
        a = a * a % m;
        b >>= 1;
    }
    return res;
}

int main(){

    int t;
    cin >> t;
    while(t){
        for(int i=0;i<t;i++){
            long long int x, y, n;
            cin >> x >> y >> n;

            long long int result = binpow(x, y, n);

            cout << result << endl;
        }
        cin >> t;
    }

    return 0;
}