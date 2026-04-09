#include <bits/stdc++.h>
using namespace std;

void solve() {
    long long n;
    cin >> n;
    vector<int> nums(n);
    for(int i=0;i<n;i++)cin >> nums[i];
    map<pair<int,int>, vector<int>> naoForamUsados; //naoForamUsados[idxDoQueJaUsou][mod] -> listaComIndicesPraSeremTest
    // vector<bool> visit(200001, false);
    long long cont = 0;
    for(int i=0;i<n;i++){
        if(nums[i] > n);
        else if(!naoForamUsados.count({nums[i], i%nums[i]})){

            for(int j=i + nums[i];j<n;j+=nums[i]){
                if(j-i == nums[i] * nums[j]){
                    cont++;
                }else{
                    naoForamUsados[{nums[i], i%nums[i]}].push_back(j); 
                }
            }

            // visit[nums[i]] = true;
        }
        else{
            for(auto aux : naoForamUsados[{nums[i], i%nums[i]}]){
                if(aux <= i) /*naoForamUsados[{nums[i], i%nums[i]}].remove(aux)*/;
                else if(aux-i == nums[i] * nums[aux]){
                    // naoForamUsados[{nums[i], i%nums[i]}].remove(aux);
                    cont++;
                }
            }
        }
    }
    cout << cont << endl;

}

int main() {
    int t;
    cin >> t;
    while (t--) {
        solve();
    }
    return 0;
}