#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        vector<int> nums(1<<n, 1);
        bool primeiro = true;
        for(int i=(1<<n)-1; i>0;i = i >> 1){
            if(primeiro) cout << i;
            else cout << " " << i;
            primeiro = false;
            nums[i] = 0;
        }
        for(int i=0;i<nums.size();i++){
            if(nums[i]){
                if(primeiro) cout << i;
                else cout << " " << i;
            }
            primeiro = false;
        }
        cout << endl;
    }


    return 0;
}