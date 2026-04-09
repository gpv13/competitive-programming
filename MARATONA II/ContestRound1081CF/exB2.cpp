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
        bool soZero = true;
        int contaUns = 0, contaZeros = 0;
        int posUm1 = -1, posUm2 = -1;
        int posZero1 = -1, posZero2 = -1;
        for(int i=0;i<n;i++){
            if(s[i] == '1'){
                contaUns++;
                soZero = false;
                if(posUm1 == -1) posUm1 = i;
                else if(posUm2 == -1) posUm2 = i;
            }else{
                contaZeros++;
                if(posZero1 == -1) posZero1 = i;
                else if(posZero2 == -1) posZero2 = i;
            }
        }
        if(soZero) cout << "0" << endl;
        else if(n%2 && contaUns%2){
            cout << "-1" << endl;
        }else{
            vector<int>op;
            if(n%2){
                char c;
                if(contaUns > contaZeros) c = '0';
                else c = '1'; 
                for(int i=0;i<n;i++){
                    if(c == s[i]) op.push_back(i);
                }
            }
            else{
                if(contaUns%2){
                    op.push_back(posZero1);
                    contaUns = contaZeros - 1;
                    contaZeros = contaUns + 1;
                    for(int i=0;i<n;i++){
                        if(i!=posZero1){
                            if(s[i] == '1')s[i] = '0';
                            else {s[i] = '1'; op.push_back(i);}
                        }
                    }
                }else{
                    for(int i=0;i<n;i++){
                        if(s[i] == '1') op.push_back(i);
                    }
                }
            }
            cout << op.size() << endl;
            bool primeiro = true;
            for(auto o : op){

                if(primeiro) cout << o+1;
                else cout << " " << o+1;
                primeiro = false;
            }
            cout << endl;

        }
    }


    return 0;
}