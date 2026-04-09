#include<bits/stdc++.h>
using namespace std;

int main(){

    long long int t;
    cin >> t;
    while(t--){

        long long int n;
        cin >> n;
        vector<long long int>nums(n);
        for(int i=0;i<n;i++){
            cin >> nums[i];
        }

        sort(nums.begin(), nums.end());
        //cout << nums[0] << endl;
        long long int mod = nums[0];

        cout << max(nums[1] - nums[0], mod) << endl;

    }


    return 0;
}