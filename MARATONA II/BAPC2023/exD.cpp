#include<bits/stdc++.h>
using namespace std;

int main(){

    int letras[27][1001];
    for(int i=0;i<27;i++){
        for(int j=0;j<1001;j++){
            letras[i][j] = 0;
        }
    }
    int n, m;
    cin >> n >> m;
    vector<string> palavras;
    for(int i=0;i<n;i++){
        string aux;
        for(int j=0;j<m;j++){

            char caux;
            cin >> caux;
            letras[caux - 'a'][j]++;

        }
        palavras.push_back(aux);
    }

    string result;
    for(int i=0;i<m;i++){
        pair<int,int> auxletra = {-1, 0};
        for(int j=0;j<27;j++){
            if(auxletra.second < letras[j][i]){
                auxletra.second = letras[j][i];
                auxletra.first = j;
            }
        }
        result += auxletra.first + 'a';
    }

    cout << result << endl;

    return 0;
}