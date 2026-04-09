#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        vector<int> nums(n);
        for(int i=0;i<n;i++){
            cin >> nums[i];
        }
        int conta = 0;
        stack<int> pilha;
        for(int i=0;i<n;i++){
            while(!pilha.empty() && pilha.top() != nums[i]-1)pilha.pop();
            if(pilha.empty()){
                conta++;
            }
            pilha.push(nums[i]);
        }
        long long maior = 0, menor = 0;
        for(int i=1;i<=n;i++){
            menor += i;
            maior += (i * (n-i +1));
        }
        long long aux = (maior-menor)/(n - 1);
        long long res = menor + (conta-1)*aux;
        cout << res<< endl;
    }


    return 0;
}