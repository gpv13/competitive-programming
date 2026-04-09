#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        string s;
        cin >> s;
        bool soZero = true, doisUns = false;
        int contaUns = 0;
        int posUm1 = -1, posUm2 = -1;
        for(int i=0;i<n;i++){
            if(s[i] == '1'){
                contaUns++;
                soZero = false;
                if(posUm1 == -1) posUm1 = i;
                else if(posUm2 == -1) posUm2 = i;
            }
        }
        if(soZero) cout << "0" << endl;
        else if(contaUns == 2){
            cout << "2" << endl;
            cout << posUm1+1 << " " << posUm2+1 << endl;
        }else{
            cout << "-1" << endl;
        }
    }


    return 0;
}