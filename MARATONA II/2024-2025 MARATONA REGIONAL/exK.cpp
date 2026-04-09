#include<bits/stdc++.h>
using namespace std;

int main(){

    long long int n;
    cin >> n;
    vector<int> lista;
    int total = 0;
    for(int i=0;i<n;i++){
        int aux;
        cin >> aux;
        total+=aux;
        lista.push_back(aux);
    }

    vector<long long int> dp(total + 1, -1e10);
    dp[0] = -1;
    if(total%2 !=0){
        cout << "-1" << endl;
    }else{

        for(int i=0;i<n;i++){
            vector<int> naopodemudar(total+1, false);

            // if(dp[lista[i]] == -1e10){
            //     dp[lista[i]] = -1;
            //     naopodemudar[lista[i]] = true;
            // }
            for(int j=dp.size() - 1;j>=1;j--){
                if((j - lista[i]) >= 0 && dp[j] == -1e10 && dp[j - lista[i]] != -1e10){
                    dp[j] = j - lista[i];
                }
            }
        }
        // for(auto nums : dp){
        //     cout << " " << nums;
        // }
        // cout << endl;
        
        vector<long long> backtrack;
        int aux = total/2;
        while(dp[aux] != -1 && dp[aux]!=-1e10){
            backtrack.push_back(aux - dp[aux]);
            aux = dp[aux];
        }
        if(aux == -1e10){
            cout << "-1" << endl;
        }else{
            vector<long long int> segundo;
            //backtrack.push_back(aux);
            long long totback = 0;
            for(auto nums : backtrack){
                totback += nums;
            }
            if(totback != total/2){
                cout << "-1" << endl;
            }else{
                int j = 0;
                sort(backtrack.begin(), backtrack.end());
                sort(lista.begin(), lista.end());
                for(int i=0;i<lista.size();i++){
                    if(j < backtrack.size() && lista[i] == backtrack[j]){
                        j++;
                    }else{
                        segundo.push_back(lista[i]);
                    }

                }

                // for(auto nums : backtrack){
                //     cout << " " << nums;
                // }
                // cout << endl;
                // for(auto nums : segundo){
                //     cout << " " << nums;
                // }
                // cout << endl << endl << endl;
                int quantprim = 0, quantsec = 0, posprim = 0, possec = 0;
                bool prim = true;
                while(quantprim != total/2 || quantsec != total/2){
                    if(!prim) cout << " ";
                    if(quantprim<=quantsec){
                        cout << backtrack[posprim];
                        quantprim+=backtrack[posprim];
                        posprim++;
                    }else{
                        cout << segundo[possec];
                        quantsec+=segundo[possec];
                        possec++;
                    }

                    prim = false;
                }
                cout << endl;
            }
            

        }
    }


    return 0;
}