#include<bits/stdc++.h>
using namespace std;
int main(){

    int n, b, p;
    cin >> n >> b >> p;
    int N = n;
    long long conta = 0;
    int porPart = 2*b + 1;
    while(n>1){
        int matches = 31 - __builtin_clz(n);
        // cout << n << endl;
        // cout << matches << endl;
        conta += ((1 << matches)/2)*porPart;
        n-= (1 << matches)/2;
    }

    cout << conta << " " << N*p << endl;
}