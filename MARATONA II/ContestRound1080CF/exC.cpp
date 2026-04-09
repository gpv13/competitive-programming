#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        vector<int> nums(n+1);
        int conta = 0;
        for(int i=1;i<=n;i++){
            cin >> nums[i];
        }
        for(int i=2;i<=n;i++){
            int imposs = 7 - nums[i-1];
            if(nums[i] == imposs || nums[i] == nums[i-1]){ 
                conta++;

                for(int j=1;j<=6;j++){
                    if(i!=n && j!=imposs && j!=(7-nums[i+1]) && j!=nums[i-1] && j!=nums[i+1]){
                        nums[i] = j;
                        break;
                    }
                }
            }
        }

        cout << conta;
        cout << endl;
        

    }


    return 0;
}