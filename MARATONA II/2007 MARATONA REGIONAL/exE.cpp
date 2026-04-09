#include<bits/stdc++.h>
using namespace std;

int main(){

    
    int t;
    cin >> t;

    while(t){

        vector<int> comandos(1000001, 0);
        int total = 0;
        for(int i=0;i<t;i++){

            int aux;
            cin >> aux;

            if(!comandos[aux]) total+= aux + (i);
            else total+= i - (comandos[aux] - 1);
            comandos[aux] = i+1;
        }

        cout << total << endl;

        cin >> t;
    }



    return 0;
}