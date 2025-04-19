#include<bits/stdc++.h>
using namespace std;

int main(){

    int n, arrows = 0, h;
    vector<int> baloons;
    cin >> n;
    for(int i=0; i<n; i++){
        cin >> h;
        baloons.push_back(h);
    }
    while(!baloons.empty()){
        int aim = baloons[0];
        for(int i=0; i<baloons.size(); i++){
            if(aim == baloons[i]){
                baloons.erase(baloons.begin() + i);
                i--;
                aim--;
            }
        }
        arrows++;
    }
    cout << arrows << endl;

    return 0;
}
