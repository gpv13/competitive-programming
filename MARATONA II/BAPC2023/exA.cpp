#include<bits/stdc++.h>
using namespace std;

int main(){

    long long int n, m, k, total = 0;
    cin >> n >> m >> k;
    vector<long long int>nums(n);
    for(int i=0;i<n;i++){

        cin >> nums[i];
        total+=nums[i];
    }
    long long int countmax = 0;
    sort(nums.rbegin(), nums.rend());
    for(int i=0;i<k+m;i++){
        countmax += nums[i];
    }
    long double result = (long double)(((long double)countmax*100.0)/(long double)total);
    
    cout << result << endl;
    return 0;
}