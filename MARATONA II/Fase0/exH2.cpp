#include<bits/stdc++.h>
using namespace std;

int main(){

    long long s;
    cin >> s;
    long long ans=s;
    bool isUnder = false;

    long long max = 1e18;

    set<long long> pot2;

    for(long long i=1;i<=max;i*=2){
        pot2.insert(i);
    }

    if(ans == 1) cout << 1 << endl;
    else if(pot2.count(ans)) cout << ans - 1 << endl;
    else{

        int quantBits = 32 - __builtin_clz(ans);
        // quantBits++;
        quantBits--;
        int num = 0;
        for(int i=quantBits;i>=0;i--){
            if(i == quantBits - i){
                if(num + (1<<i) <= ans) num += (1<<i);
            }
            else if(num + (1 << i) + (1 << (quantBits - i))<= ans){
                num += (1<<i) + (1<<(quantBits-i));
            }
        }
        cout << num << endl;
    }



    return 0;
}