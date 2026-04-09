#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n, k;
        cin >> n >> k;
        int numErros = k-n;

        if(numErros >= n || numErros < 0){
            cout << "NO" << endl;
        }else{
            int numMeio = n/2;
            int numPrimErros = (k - n)/2;
            bool errosExtras = false;
            vector<int> nums(n, -1);
            if(numErros > numMeio) errosExtras = true;

            stack<int>erros;
            stack<int> acertos;
            bool taNoErro = true;
            bool f = true;
            if(!errosExtras){
                cout << "YES" << endl;
                int contaErros = 0;
                for(int i=0;i<n;i++){
                    if(contaErros == numErros) taNoErro = false;

                    if(taNoErro)erros.push(i+1);
                    else acertos.push(i+1);
                    
                    if(taNoErro){
                        if(!f) cout << " " << i+1;
                        else {cout << i+1; f = false;}
                    }
                    
                    if(i%2) contaErros++;
                }
                while(!acertos.empty()){
                    if(!f) cout << " ";
                    else f = false;
                    cout << acertos.top() << " " << acertos.top();
                    acertos.pop();
                }
                while(!erros.empty()){
                    if(!f) cout << " ";
                    else f = false;
                    cout << erros.top();
                    erros.pop();
                } 
                cout << endl;
            }else{

                cout << "YES" << endl;
                int contaErrosExtras = k - n - n/2;
                int posParada = (n - contaErrosExtras*2);

                vector<int> resp;
                int conta = 1;
                for(int i=0;i<posParada;i++){

                    resp.push_back(conta);
                    erros.push(conta);
                    conta++;
                    resp.push_back(conta);
                    erros.push(conta);
                    conta++;

                }
                for(int i=posParada;i<k-n;i++){
                    resp.push_back(conta);
                    acertos.push(conta);
                    conta++;
                    resp.push_back(erros.top());
                    erros.pop();
                }
                cout << "a";
                while(!acertos.empty()){
                    resp.push_back(acertos.top());
                    acertos.pop();
                }
                while(!erros.empty()){
                    resp.push_back(erros.top());
                    erros.pop();
                }

                for(int i=0;i<n;i++){
                    if(!i) cout << resp[i];
                    else cout << " " << resp[i];
                }
                cout << endl;
                // int contaErros = 0;
                // for(int i=0;i<2*(numErros-numPrimErros);i++){
                //     if(taNoErro)erros.push(i+1);
                //     else acertos.push(i+1);
                //     if(i) cout << " " << i+1;
                //     else cout << i+1;
                //     if(i%2) contaErros++;
                //     if(contaErros == numErros) taNoErro = false;
                //     // cout << "primfor";
                // }
                // int aux = 2*2*(numErros-numPrimErros) + 1; 
                // // cout << "aux : ( "  << aux << ")";
                // for(int i=2*2*(numErros-numPrimErros);i<2*n;i++){
                //     // cout << "secfor";
                //     if(contaErros == numErros) taNoErro = false;
                //     if(!taNoErro) break;
                //     if(!(i%2)){
                //         acertos.push(aux);
                //         cout << " " << aux++;
                //     }else{
                //         cout << " " << erros.top();
                //         erros.pop();
                //     }
                //     if(i%2) contaErros++;

                // }
                // while(!acertos.empty()){
                //     cout << " "<< acertos.top();
                //     acertos.pop();
                // }
                // while(!erros.empty()){
                //     cout << " "<< erros.top();
                //     erros.pop();
                // } 
                // cout << endl;

            }

        }
        
    }


    return 0;
}