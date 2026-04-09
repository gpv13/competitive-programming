#include<bits/stdc++.h>
using namespace std;
int main(){

    int n, c;
    cin >> n >> c;
    vector<string> palavras(n);
    map<string, int> dic;
    for(int i=0;i<n;i++){
        cin >> palavras[i];
        int posAst = -1;
        for(int j=0;j<c;j++){
            if(palavras[i][j] == '*'){
                posAst = j;
                break;
            }
        }
        for(int j=0;j<26;j++){
            string aux;
            for(int k=0;k<c;k++){
                if(palavras[i][k] == '*'){
                    aux+= j + 'a';
                }else{
                    aux += palavras[i][k];
                }
            }
            dic[aux]++;
        }
    }
    string melhor;
    int melhorVal = -1;
    for(auto s : dic){
        if(s.second > melhorVal){
            melhorVal = s.second;
            melhor = s.first;
        }
    }  
    cout << melhor << " " << melhorVal << endl;

    return 0;
}