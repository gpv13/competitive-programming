#include<bits/stdc++.h>
using namespace std;
 
int main(){
 
 
    int n, t, result;
    long long int maior = 0, menor = 1000000001, ovelha;
    cin >> t;
    for(int i= 0; i<t; i++){
        cin >> n;
        maior = 0;
        menor = 1000000001;
        for(int j=0; j<n; j++){
            cin >> ovelha;
            if(ovelha > maior){
                maior = ovelha;
            }
            if(ovelha < menor){
                menor = ovelha;
            }
        }
        result = maior - menor;
        cout << result << endl;
    }
 
 
    return 0;
}