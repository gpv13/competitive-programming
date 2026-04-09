#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    vector<long long int>locais;
    while(n--){
        int aux;
        cin >> aux;
        locais.push_back(aux);
    }  
    long long int teleporte = 0, localatual = locais[0];
    long long int total = locais[0];
    for(int i=1;i<locais.size();i++){
        if(localatual == locais[i]){
            continue;
        }
        else if(abs(locais[i] - teleporte) <= abs(locais[i] - localatual)){
            
            total += abs(locais[i] - teleporte);
            teleporte = localatual;

        }
        else{
            total += abs(locais[i] - localatual);
        }
        localatual = locais[i];
    }
    cout << total << endl;



    return 0;
}