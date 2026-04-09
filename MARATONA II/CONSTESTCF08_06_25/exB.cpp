#include<bits/stdc++.h>
using namespace std;

int main(){

    int q;
    cin >> q;
    
    for(int i=0;i<q;i++){
        int n;
        cin >> n;
        vector<int> ord(n+1);
        ord[1] = 1;
        ord[n] = 2;
        for(int i=2;i<n;i++){
            ord[i] = i+1;
        }
        bool first = true;
        for(int i=1;i<=n;i++){
            if(!first) cout << " ";
            cout << ord[i];
            first = false; 
        }
        cout << endl;
    }

    
    return 0;
}