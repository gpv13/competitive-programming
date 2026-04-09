#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        long long menorK = LLONG_MAX;
        long long menor = LLONG_MAX, maior = -1;
        int n;
        cin >> n;
        vector<long long> nums(n);
        for(int i=0;i<n;i++){
            cin >> nums[i];
            maior = max(maior, nums[i]);
            menor = min(menor, nums[i]);
        }

        vector<long long> numsSort = nums;
        sort(numsSort.begin(), numsSort.end());

        for(int i=0;i<n;i++){
            if(numsSort[i] != nums[i]){
                long long aux = max(abs(maior-numsSort[i]), abs(menor-numsSort[i]));
                menorK = min(menorK, aux);
            }
        }
        if(menorK == LLONG_MAX)cout << "-1";
        else cout << menorK;

        cout << endl;
    } 

    return 0;
}