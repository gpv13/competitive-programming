#include<bits/stdc++.h>
using namespace std;
int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        string cadeiras;
        cin >> cadeiras;
        bool nice[n] = {false};
        int contaUns = 0, contaZeros = 0;
        for(int i=0;i<cadeiras.size();i++){
            if(cadeiras[i] == '1'){
                contaUns++;
                nice[i] = true;
            }else{
                if(i && cadeiras[i-1] == '1') nice[i] = true;
                if(i < cadeiras.size()-1 && cadeiras[i+1] == '1') nice[i] = true;
                // contaZeros++;
            }
        }

        for(int i=0;i<n;i++){
            if(!nice[i]){
                nice[i] = true;
                int conta=2;
                while(conta-- && ++i <n && !nice[i]){
                    nice[i] = true;
                }
                contaZeros++;
            }
        }

        cout << contaUns + contaZeros << endl;
        // else{
        //     cout << contaUns + (contaZeros/2) << endl;
        // }
    }


    return 0;
}