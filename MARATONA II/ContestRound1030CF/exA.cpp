#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    for(int i=0;i<n;i++){
        int t, k;
        cin >> t >> k;

        for(int j=0;j<k;j++){
            cout << "1";
        }
        for(int j=0;j<t-k;k++){
            cout << "0";
        }

        cout << endl;

    }


    return 0;
}