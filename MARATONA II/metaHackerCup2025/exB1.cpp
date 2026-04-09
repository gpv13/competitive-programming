#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    for(int i=1;i<=t;i++){

        int n,a,b;
        cin >> n >> a >> b;
        cout << "Case #" << i << ":";
        for(int j=1;j<2*n;j++){
            cout << " 1"; 
        }
        cout << " " << b << endl;
    }



    return 0;
}