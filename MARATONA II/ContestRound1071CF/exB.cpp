#include<bits/stdc++.h>
using namespace std;

vector<int>news(200001);

int solve(vector<int> nums,vector<int> diffs, int t){
    int maior = 0;
    news[0] = diffs[0];
    maior = max(maior, news[0]);
    news[t] = diffs[t-2];
    maior = max(maior, news[t]);
    for(int i=1;i<t-1;i++){
        news[i] = (diffs[i] + diffs[i-1]) - abs(nums[i+1] - nums[i-1]);
        maior = max(maior, news[i]);
    }
    // cout << "diffs: ";
    // for(int i=0;i<t;i++){
    //     cout << news[i] << " ";
    // }
    return maior;
}

int main(){

    int n;
    cin >> n;

    while(n--){

        int t;
        cin >> t;
        vector<int>nums(t);
        for(int i=0;i<t;i++){
            int aux;
            cin >> aux;
            nums[i] = aux;
        }
        vector<int> diffs(t-1);
        int total = 0;
        for(int i=0;i<t-1;i++){
            diffs[i] = abs(nums[i] - nums[i+1]);
            total += abs(nums[i] - nums[i+1]);
        }
        int res = solve(nums, diffs, t);
        //cout << total << " " << res << endl;
        cout << total - res << endl;
    }


    return 0;
}