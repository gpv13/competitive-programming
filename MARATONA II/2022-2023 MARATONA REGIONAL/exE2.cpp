#include<bits/stdc++.h>
using namespace std;
vector<int> baloons;
int main(){

    int n, h, inc = 0, count = 0;
    cin >> n;
    for(int i=0;i<n;i++){
        inc = 0;
        cin >> h;
        if(baloons.empty()){
            baloons.push_back(h);
            inc++;
            count++;  
        }
        if(!inc){
            for(int i =0; i<baloons.size(); i++){
                if(h == baloons[i] - 1){
                    baloons[i]--;
                    if(baloons[i] == 0){
                        baloons.erase(baloons.begin() + i);
                    }
                    inc++;
                    break;
                }
            }
            if(!inc){
                    baloons.push_back(h);
                    count++;
                    inc++;
            }
        }
    }
    cout << count << endl;

    return 0;
}