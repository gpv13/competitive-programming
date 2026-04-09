#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        vector<int>nums(n);
        int posMaior = -1, maior = -1;
        for(int i=0;i<n;i++){cin >> nums[i]; if(nums[i] > maior){maior = nums[i]; posMaior = i;}}

        if(posMaior!=0){nums[0] ^= nums[posMaior];
        nums[posMaior] ^= nums[0];
        nums[0] ^= nums[posMaior];}
        for(int i=0;i<n;i++){
            if(!i) cout << nums[i];
            else cout << " " << nums[i];
        }cout << endl;
    }


    return 0;
}