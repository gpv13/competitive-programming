#include<bits/stdc++.h>
using namespace std;

#define MOD 676767677

int main(){

    int t;
    cin >> t;
    while(t--){
        int n, k;
        cin >> n >> k;
        vector<int> a(n), b(n);
        vector<int> posicoes (n+1);
        for(int i=0;i<n;i++){ 
            cin >> a[i];
            posicoes[a[i]] = i;
        }
        for(int i=0;i<n;i++) cin >> b[i];
        bool certo = true;
        for(int i=0;i<n;i++){
            if(b[i] == -1) continue;
            if(posicoes[b[i]] == -1){
                certo = false;
                break;
            }
            if(i <= posicoes[b[i]]){
                if(abs(min(posicoes[b[i]] + k - 1, n-1) - i) >= k){
                    certo = false;
                    break;
                }
            }else{
                if(abs(max(posicoes[b[i]] - k + 1, 0) - i) >= k){
                    certo = false;
                    break;
                }
            }
            posicoes[b[i]] = -1;
        }

        if(!certo){
            cout << "NO" << endl;
            continue;
        }

        //posicoes, 
        priority_queue<int> pq;
        for(int i=1;i<=n;i++){
            if(posicoes[i] != -1){
                pq.push(posicoes[i]);
            }
        }

        for(int i=n-1;i>=0;i--){
            if(b[i] == -1){
                if(i <= pq.top()){
                    if(abs(min(pq.top() + k - 1, n-1) - i) >= k){
                        certo = false;
                        break;
                    }
                }else{
                    if(abs(max(pq.top() - k + 1, 0) - i) >= k){
                        certo = false;
                        break;
                    }
                }
                pq.pop();
            }
        }

        if(certo) cout << "YES" << endl;
        else cout << "NO" << endl;


    }


    return 0;
}