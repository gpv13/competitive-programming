#include<bits/stdc++.h>
using namespace std;

int main(){

    vector<int> pre;
    int a = 1;
    int auxdois = 2;
    while(a <= 1000000000){
        pre.push_back(a);
        a+=auxdois;
        auxdois *= 2;
    }
    

    int t;
    cin >> t;
    for(int z=0;z<t;z++){
        vector<int> nums;
        int n, k;

        cin >> n >> k;

        for(int i=0;i<n;i++){
            int aux;
            if(aux%2==0 && k!=0){
                aux++;
                k--;
            }
            nums.push_back(aux);
        }

        for(int n : nums){
            
        }

    }


    return 0;
}