#include<bits/stdc++.h>
using namespace std;
#define INF 3000000000
int main(){

    long long int t;
    cin >> t;
    while(t--){

        long long int n, c;
        cin >> n >> c;
        vector<long long int> nums(n);
        for(long long int i=0;i<n;i++){
            cin >> nums[i];
        }
        long long int zeros = 0;
        bool certo = true;
        while(certo){
            bool mudanca = false;
            sort(nums.begin(), nums.end());
            bool achou = false;
            for(long long int i=n-1;i>=0;i--){
                if(nums[i] > c){

                    continue;
                }else if(!achou){
                    zeros++;
                    nums[i] = INF;
                    achou = true;
                }
                else{
                    mudanca = true;
                    nums[i] *= 2;
                }
            }

           
            if(!mudanca) certo = false;
        }
        cout << n-zeros << endl;
    }


    return 0;
}