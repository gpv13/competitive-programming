#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        int max = -1;
        int quant = 0;
        cin >> max;
        for(int i=1;i<n;i++){
            int aux;
            cin >> aux;
            if(aux < max) quant++;
            if(aux > max) max = aux;
        }
        cout << quant << endl;
    }


    return 0;
}