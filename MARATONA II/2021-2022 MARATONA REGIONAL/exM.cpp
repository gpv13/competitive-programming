#include<bits/stdc++.h>
using namespace std;

int main(){
    
    int q;
    cin >> q;
    int numHumanos = 1;
    vector<stack<int>> filhos(q+3);
    vector<bool> vivo(q+3, true);
    stack<int> succ;
    int reiAtual = 1;
    for(int i =0;i<q;i++){

        int op, id;
        cin >> op >> id;

        if(op == 1){
            filhos[id].push(++numHumanos);
        }else{
            vivo[id] = false;

            if(id == reiAtual){

                while(!filhos[id].empty()){
                    succ.push(filhos[id].top());
                    filhos[id].pop();
                }

                while(!vivo[succ.top()]){ 
                    int morto = succ.top();
                    succ.pop();

                    while(!filhos[morto].empty()){
                        succ.push(filhos[morto].top());
                        filhos[morto].pop();
                    }
                }
                
                reiAtual = succ.top();
                succ.pop();
            }

            cout << reiAtual << endl;
        }

    }
    

    return 0;
}