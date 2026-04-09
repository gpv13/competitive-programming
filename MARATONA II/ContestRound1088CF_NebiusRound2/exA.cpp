#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        vector<int> nums(n);
        for(int i=0;i<n;i++) cin >> nums[i];
        vector<int> ans(n);
        if(n == 1){
            cout << "1" << endl;
            continue;
        }
        for(int i=0;i<n;i++){
            if(!i)cout << "2";
            else cout << " 2";
        }cout << endl;
    }


    return 0;
}