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
        
        string ans;
        int pointL = 0, pointR = n-1;
    
        for(int i=0;i<n;i++){
            if(i%2){

                if(nums[pointR] > nums[pointL]){
                    ans += "R";
                    pointR--;
                }else{
                    ans+="L";
                    pointL++;
                }

            }else{

                if(nums[pointR] < nums[pointL]){
                    ans += "R";
                    pointR--;
                }else{
                    ans+="L";
                    pointL++;
                }

            }
        }
        cout << ans << endl;
    }


    return 0;
}