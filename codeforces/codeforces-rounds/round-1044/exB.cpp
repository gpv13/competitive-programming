//correct
#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        vector<int> villagers(n);
        for(int i=0;i<n;i++){

            cin >> villagers[i];

        }
        sort(villagers.begin(), villagers.end(), greater<int>());
        long long int count = 0;
        for(int i=0;i < (n%2 == 0 ? n : n-1); i+=2){
            count += max(villagers[i], villagers[i+1]);
        }
        if(n%2 != 0) count += villagers.back();
        cout << count << endl;
    }


    return 0;

}