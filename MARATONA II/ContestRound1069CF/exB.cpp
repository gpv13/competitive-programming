#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;

    while(t--){

        int n;
        cin >> n;
        int l, r;
        cin >> l >> r;
        vector<int> pre;
        pre.push_back(0);
        for(int i=1;i<=n;i++){
            pre.push_back(i);
        }
        pre[l-1] = r;
        vector<int> real(n+1);
        for(int i=1;i<=n;i++){
            real[i] = pre[i] ^ pre[i-1];
        }
        
        for(int i=1;i<=n;i++){
            if(i==1) cout << real[i];
            else cout << " " << real[i];
        }
        cout << endl;
    }


    return 0;
}