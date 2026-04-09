#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        vector<int> nums(n+1);
        bool deuErrado = false;
        for(int i=1;i<=n;i++){
            cin >> nums[i];
            int x = __builtin_ctz(i);
            int y = __builtin_ctz(nums[i]);
            // cout << x << " "  << y << endl;
             
            int xx = i >> x;
            
            int yy = nums[i] >> y;
            // cout << xx << " " << yy << endl;
            if(xx != yy) deuErrado = true;  
        }
        if(deuErrado) cout << "NO";
        else cout << "YES";
        cout << endl;
        

    }


    return 0;
}