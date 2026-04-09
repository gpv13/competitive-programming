#include<bits/stdc++.h>

using namespace std;

int main(){

    int t;
    cin >> t;
    for(int k=0;k<t;k++){

        vector<int> b, c;
        int n;
        cin >> n;
        for(int i=0;i<n;i++){
            int aux;
            cin >> aux;
            b.push_back(aux);
        }
        c = b;
        vector<int> result;
        bool vdd = false;
        sort(b.begin(), b.end());
        for(int i=0;i<n;i++){
            if(c[i] != b[i]){
                vdd = true;
                result.push_back(c[i]);
            }
        }
        if(vdd){
            cout << "YES" << endl << result.size() << endl;
            bool first = true;
            for(int i : result){
                if(first) cout << i;
                else cout << " " << i;
                first = false; 
            }
            cout << endl;
        }
        else cout << "NO" << endl;
    }



    return 0;
}