#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        cout << "2";
        for(int i=0;i<n-2;i++){
            cout << " " << n-i; 
        }
        cout << " 1" << endl;
    }

    return 0;
}