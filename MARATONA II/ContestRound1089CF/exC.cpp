#include<bits/stdc++.h>
using namespace std;

int mmc(int m, int n){
    return (m * n) / __gcd(m, n);
}

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        vector<int> a(n), b(n);
        for(int i=0;i<n;i++){
            cin >> a[i];
        }
        for(int i=0;i<n;i++){
            cin >> b[i];
        }

        int ans = 0;
        for(int i=0;i<n;i++){
            bool frontTrue = true, backTrue = true;
            int front = 1, back = 1;
            if(i != n-1){
                if(__gcd(a[i], a[i+1]) == a[i]) frontTrue = false;
                else front = __gcd(a[i], a[i+1]);
            }
            if(i!=0){
                if(__gcd(a[i], a[i-1]) == a[i]) backTrue = false;
                else back = __gcd(a[i], a[i-1]);
            }
            if(frontTrue && backTrue && mmc(front, back) < a[i]) ans++;
        }
        cout << ans << endl;

    }


    return 0;
}