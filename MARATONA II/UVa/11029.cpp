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
    while(t--){

            long long int x, y;
            cin >> x >> y;
            float p = y * log10(x);
            float ex = p - floor(p);
            float pre = pow(10, ex) * 100;
            long long int inpre = floor(pre); 
            long long int pos = binpow(x, y, 1000);



            cout << inpre << "..." << pos << endl;
    }

    return 0;
}