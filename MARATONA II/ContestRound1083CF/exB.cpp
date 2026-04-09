#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        long long n;
        cin >> n;
        set<long long>div;

        while (n % 2 == 0) {
            div.insert(2);       
            n = n / 2;
        }

        for (long long i = 3; i * i <= n; i += 2) {
            while (n % i == 0) {
                div.insert(i);
                n = n / i;
            }
        }

        if (n > 2) {
            div.insert(n);
        }
        long long res = 1;
        for(auto s : div) res *= s;
        cout << res << endl;
    }


    return 0;
}