#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        bool temUm = false, tem67 = false;   
        for(int i=0;i<n;i++){
            int aux;
            cin >> aux;
            if(aux == 67) tem67 = true;
        }
            if(tem67) cout << "YES" << endl;
            else cout << "NO" << endl;
    }


    return 0;
}