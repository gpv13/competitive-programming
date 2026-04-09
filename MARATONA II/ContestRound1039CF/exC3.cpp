#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        vector<int>nums(n);
        vector<int> minPre(n, 0);
        for(int i=0;i<n;i++){
            cin >> nums[i];
            minPre[i] = nums[i];
            if(i>0) minPre[i] = min(minPre[i], minPre[i-1]);
        }
        bool certo = true;
        for(int i=1;i<n;i++){
            if(nums[i] > minPre[i-1] + minPre[i-1] - 1){
                certo = false;
                break;
            }
        }
        if(certo) cout << "YES";
        else cout << "NO";
    
        cout << endl;
    }

    return 0;
}