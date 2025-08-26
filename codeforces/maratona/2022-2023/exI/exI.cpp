//correct
#include<bits/stdc++.h>
using namespace std;

int main(){
    bool vdd = true;
    for(int i=0; i<8; i++){
        int n;
        cin >> n;
        if(n==9){
            vdd = false;
        }
    }  
    if(vdd){
        cout << "S" << endl;
    }else{
        cout << "F" << endl;
    }
    

    return 0;
}
