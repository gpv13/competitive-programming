#include<bits/stdc++.h>
using namespace std;

int main(){

    ios::sync_with_stdio(false);
    cin.tie(NULL);
    
    long long int t;
    cin >> t;
    while(t--){

        long long int n;
        cin >> n;
        vector<long long int> odds, evens;
        for(long long int i=0;i<n;i++){
            long long int aux;
            cin >> aux;

            if(aux%2) odds.push_back(aux);
            else evens.push_back(aux);
        }
        //cout << odds.size() <<  " " << evens.size() << endl;
        if(odds.size()>0)sort(odds.begin(),odds.end());
        if(evens.size()>0)sort(evens.begin(), evens.end());
        //cout << odds.size() <<  " " << evens.size() << endl;
        if(odds.size() == 0){
            for(long long int i=0;i<n;i++){
                if(!i) cout << "0";
                else cout << " 0";
            }
            cout << endl;
        }
        else{
            //cout << "oi";
            vector<long long int>ans(n+1);
            ans[1] = odds[odds.size()-1];
            ans[0] = 0;
            for(long long int i=1;i<=evens.size();i++){
                //cout << "oi2";
                ans[i+1] = ans[i] + evens[(int)evens.size()-i];
            }
            //cout << "oi3";
            long long int quant = odds.size() - 2;
            //cout << "OI4";
            for(long long int i=evens.size()+1;i<=quant+(long long int)evens.size();i++){
                ans[i+1] = ans[i-1];
            }
            //cout << "oi";
            if(n>=2 && odds.size()>1){
                //cout << "ok";
                if(!(odds.size()%2)) ans[n] = 0;
                else ans[n] = ans[n-2];
            }
            
            for(long long int i=1;i<=n;i++){
                if(i==1) cout << ans[i];
                else cout << " " << ans[i];
            }
            cout << endl;
        }

    }


    return 0;
}