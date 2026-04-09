#include<bits/stdc++.h>
using namespace std;

#define MOD 676767677

int main(){

    int t;
    cin >> t;
    while(t--){
        int x, y;
        cin >> x >> y;
        
        if(x == y){
            cout << "1" << endl;
            for(int i=0;i<x+y;i++){
                if(i) cout << " ";
                if(i<x) cout << "1";
                else cout << "-1";
            }
            cout << endl;
            continue;
        }

        long long ans = abs(x-y);
        long long divisores = 1;
        

        for(long long i = 2; i * i <= ans; i++){
            if(ans % i == 0){
                long long expoente = 0;
                while(ans % i == 0){
                    ans /= i;
                    expoente++;
                }
                divisores = (divisores*(expoente + 1)) % MOD;
            }
        }
        
        if(ans > 1){
            divisores = (divisores * 2) % MOD;
        }

        cout << divisores%MOD << endl;
        for(int i=0;i<x+y;i++){
            if(i) cout << " ";
            if(i<x) cout << "1";
            else cout << "-1";
        }
        cout << endl;
    }


    return 0;
}