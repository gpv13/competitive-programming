//correct
#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        set<int> gears;
        int n;
        cin >> n;
        bool correct = false;
        for(int i=0;i<n;i++){
            int teeth;
            cin >> teeth;

            if(gears.count(teeth)) correct = true;
            else gears.insert(teeth);
        }
        if(correct) cout << "YES" << endl;
        else cout << "NO" << endl;
    }


}