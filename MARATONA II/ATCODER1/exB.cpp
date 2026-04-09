#include<bits/stdc++.h>
using namespace std;

int main(){

    string t, u;
    cin >> t;
    cin >> u;
    bool check = false;
    for(int i =0;i<t.length() - u.length() + 1;i++){
        bool vdd = true;
        for(int j=0;j<u.length();j++){
            if(u[j] == t[i + j] || t[i+j] == '?'){
                continue;
            }else{
                vdd = false;
            }
        }
        if(vdd) check = true;
    }
    if(check){
        cout << "Yes" << endl;
    }else{
        cout << "No" << endl;
    }
    return 0;
}