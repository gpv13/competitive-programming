#include<bits/stdc++.h>
using namespace std;
int main(){

    int n;
    cin >> n;
    vector<int> nums(n);
    for(int i=0;i<n;i++)cin>>nums[i];
    
    int q;
    cin >> q;

    vector<int> nimbers(10002, 0);

    for(int i=1;i<=10000;i++){
        int mex = 0;
        set<int> jaUtil;
        for(int j=0;j<n;j++){
            if(nums[j] <= i){

                jaUtil.insert(nimbers[i-nums[j]]);
                if(nimbers[i-nums[j]] == mex){
                    mex++;
                    while(jaUtil.count(mex)) mex++;
                }
            }
        }
        nimbers[i] = mex;
    }
    string ans;
    while(q--){

        int t;
        cin >> t;
        int xr = 0;
        for(int i=0;i<t;i++){
            int aux;
            cin >> aux;
            xr ^= nimbers[aux];
        }
        if(xr) ans += "W";
        else ans += "L";
    }
    cout << ans << endl;


    return 0;
}