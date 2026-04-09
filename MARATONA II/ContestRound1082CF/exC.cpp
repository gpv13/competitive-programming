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
        cout<< conta << endl;

    }


    return 0;
}