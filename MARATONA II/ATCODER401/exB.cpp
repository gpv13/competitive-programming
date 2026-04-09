#include<bits/stdc++.h>
using namespace std;
int main(){

    int s;
    int total = 0;
    bool login = false;
    cin >> s;
    for(int i=0;i<s;i++){
        string op;
        cin >> op;
        
        if(op == "login"){
                login = true;
        }
        if(op == "logout"){
                login = false;
        }
        if(op == "private"){
                if(!login){
                    total++;
                }
        }
    }
    cout << total << endl;


    return 0;
}