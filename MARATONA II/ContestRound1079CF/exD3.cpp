#include<bits/stdc++.h>
using namespace std;

int main(){

    long long int t;
    cin >> t;
    while(t--){

        long long int n;
        cin >> n;
        vector<long long int>nums(n);
        for(long long int i=0;i<n;i++){
            cin >> nums[i];
        }
        long long int conta = 0;
        for(long long int i=0;i<n;i++){
            if(nums[i] > 200000) continue;
            for(long long int j= max(i%nums[i], i - (nums[i]*nums[i]));j<min(i+nums[i]*nums[i], n); j+=nums[i]){
                if(j<i){
                    if(abs(j-i) == nums[i]*nums[j]){
                        conta++;
                    }
                }else{
                    if(nums[i] != nums[j]){
                        if(abs(j-i) == nums[i]*nums[j]){
                            conta++;
                        }
                    }
                }
            }
        }
        cout << conta << endl;

    }


    return 0;
}