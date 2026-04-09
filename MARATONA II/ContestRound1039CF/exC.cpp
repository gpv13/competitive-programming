#include<bits/stdc++.h>
using namespace std;
#define INF 2000000000
int main(){

    long long int t;
    cin >> t;
    while(t--){
        long long int n, menor = INF;
        cin >> n;
        bool certo = true;
        cin >> menor;
        for(long long int i=1;i<n;i++){
            long long int aux;
            cin >> aux;
            if(i==0) menor = aux;
            if(aux >= 2LL * menor){
                certo = false;
                break;
            } 

            if(aux<menor) menor = aux;
            
        }
        if(certo) cout << "YES" << endl;
        else cout << "NO" << endl;
    }




    return 0;
}