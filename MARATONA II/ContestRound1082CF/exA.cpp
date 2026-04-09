#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int x, y;
        cin >> x >> y;

        int rest;
        if(y < 0){
            rest = x - (y*-4);
        }else{
            rest = x - (y*2);
        }
        if(rest < 0 || rest%3){
            cout << "NO" << endl;
        }else{
            cout << "YES" << endl;
        }
    }


    return 0;
}