#include<bits/stdc++.h>
using namespace std;

int main(){

    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    int t;

    cin >>t;
    while(t--){
        
        int n, m;
        cin >> n >> m;
        vector<int> temEsseNum(n+m+1, 0);
        for(int i=0;i<n;i++){
            int aux;
            cin >> aux;
            if(aux!=0)temEsseNum[aux]++;
        }
        vector<int> nums(m);
        for(int i=0;i<m;i++) cin >> nums[i];

        vector<int> isDivisor(n+m+1, 0);
        for(int i=1;i<=n+m;i++){
            if(!temEsseNum[i]) continue;
            for(int j = i; j<=n+m; j+=i) isDivisor[j]+=temEsseNum[i];

        }
        int contaAli = 0;
        int contaBob = 0;
        int contaDois = 0;
        for(int i=0;i<m;i++){
            if(isDivisor[nums[i]] == n) contaAli++;
            else if(!isDivisor[nums[i]])contaBob++;
            else contaDois++;
        }
        int aux = contaDois/2;
        // cout << contaDois << " "<<contaAli << " "<<contaBob << endl;
        contaDois-=aux;
        contaBob+=aux;
        contaAli +=contaDois;
        if(contaAli>contaBob){
            cout << "Alice" << endl;
        }else{
            cout << "Bob" << endl;
        }

    }

    return 0;
}