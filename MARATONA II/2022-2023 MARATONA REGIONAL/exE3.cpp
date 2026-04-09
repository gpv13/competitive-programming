#include<bits/stdc++.h>
using namespace std;
#define N 5000001
int main(){

    int n;
    int quant = 0;
    cin >> n;
    vector<int> flechas(N, 0);
    for(int i=0;i<n;i++){
        int aux;
        cin >> aux;
        if(flechas[aux] > 0){
            flechas[aux]--;
            flechas[aux-1]++;
        }
        else{
            flechas[aux-1]++;
            quant++;
        }
    }
    
    cout << quant << endl;


    return 0;
}

