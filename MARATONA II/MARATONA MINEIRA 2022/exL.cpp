#include<bits/stdc++.h>
using namespace std;

int main(){

    string cifra;
    int n;
    cin >> cifra;
    cin >> n;
    vector<int> quants(n);
    int aux = 0;
    bool subindo = false;
    int col = 0;
    if(n==1){
        cout << cifra << endl;
    }
    else{
        
        while(aux < cifra.size()){

            quants[col]++;

            if(col == 0 && subindo) subindo = false;
            if(col == n-1 && !subindo) subindo = true;

            if(subindo)col--;
            else col++;
            aux++;
        }
        
        vector<int> comecos(n);
        comecos[0] = 0;
        for(int i=1;i<n;i++){
            comecos[i] = comecos[i-1] + quants[i-1];
        }

        col = 0;
        subindo = false;
        aux = 0;
        string resp;
        vector<int> conta(n, 0);
        while(aux < cifra.size()){
            resp += cifra[comecos[col] + conta[col]];
            conta[col]++;

            if(col == 0 && subindo) subindo = false;
            if(col == n-1 && !subindo) subindo = true;

            if(subindo)col--;
            else col++;
            aux++;
        }
        cout << resp << endl;    
    }

    return 0;
}