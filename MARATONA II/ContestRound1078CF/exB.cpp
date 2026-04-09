#include<bits/stdc++.h>
using namespace std;
int main(){

    long long int t;
    cin >> t;
    while(t--){
        long long int n, x, y;
        cin >> n >> x >> y;
        vector<int>money(n);
        vector<int> transfer(n);
        for(int i=0;i<n;i++) {cin >> money[i]; transfer[i] = money[i]/x;}

        long long total=0;
        for(int i=0;i<n;i++){
            total+= transfer[i] * y;
        }

        long long melhor = 0;
        for(int i=0;i<n;i++){
            long long caso = money[i] + (total - transfer[i]*y);
            melhor = max(melhor,caso);
        }
        cout << melhor << endl;

    }

    return 0;
}