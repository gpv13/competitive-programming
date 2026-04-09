#include<bits/stdc++.h>
using namespace std;

int mmc(int m, int n){
    return (m * n) / __gcd(m, n);
}

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        string a, b;
        cin >> a >> b;
        int depth = -1;
        vector<int> layersA(n/2, 0), layersB(n/2, 0);
        stack<int> aS, bS;
        int maxDepth = 0;
        for(int i =0;i<n;i++){

            if(a[i] == '('){
                depth++;
                aS.push(depth);
                maxDepth = depth;
                // cout << "M : " << maxDepth<<endl;
            }else{
                // cout << maxDepth << " - " << aS.top() << endl;
                layersA[maxDepth - aS.top()]++;
                maxDepth = aS.top();
                aS.pop();
                depth--;
            }
        }
        depth = -1;
        maxDepth = 0;
        for(int i =0;i<n;i++){

            if(b[i] == '('){
                depth++;
                bS.push(depth);
                maxDepth = depth;
                // cout << "M : " << maxDepth<<endl;
            }else{
                // cout << maxDepth << " - " << aS.top() << endl;
                layersB[maxDepth - bS.top()]++;
                maxDepth = bS.top();
                bS.pop();
                depth--;
            }
        }

        bool errado = false;
        for(int i=0;i<layersA.size();i++){
            if(layersA[i] != layersB[i]){
                errado = true;
                break;
            }
        }
        if(errado) cout <<"NO" << endl;
        else cout << "YES" << endl;
    }


    return 0;
}