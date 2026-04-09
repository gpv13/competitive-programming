#include<bits/stdc++.h>
using namespace std;

vector<pair< char , pair<int , int>>> queries(100001);
int soma = 0;
vector<pair<char, pair<int, int>>> aux;
int encontrar(char op, int v, int x){
    
    if(v!=0){

        if(op == 'D') soma++;
        else aux.push_back(make_pair(op, make_pair(v, x)));
        int nsei = encontrar(queries[v-1].first, queries[v-1].second.first, queries[v-1].second.second);
        return nsei;
    }
    if(v==0){
        aux.push_back(make_pair(op, make_pair(v, x)));
        int last;
        for(int j =0;j<soma;j++){
            last = aux.back().second.second;
            aux.pop_back();
        }
        return last;
    }

}

int main(){

    int t;
    cin >> t;
    for(int i=0;i<t;i++){

        char op;
        int v, x;
        cin >> op >> v;
        if(op == 'E') cin >> x;

        if(op == 'E') queries[i] = {op, {v, x}};
        if(op == 'D'){
            
            queries[i] = {op, {v, 0}};

            cout << encontrar(op, v, 0) << endl;
            aux.clear();
            soma = 0;
        } 
        
    }

    return 0;
}