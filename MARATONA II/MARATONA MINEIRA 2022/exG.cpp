#include<bits/stdc++.h>
using namespace std;



int main(){

    int n;
    cin >> n;
    string game;
    cin >> game;
    bool startWithHole = false;
    if(game[0] == '.') startWithHole = true;

    if(startWithHole) cout << "-1" << endl;
    else{
        vector<int> holes, solid;
        int holeSize = 0, solidSize = 0;
        for(int i=0;i<game.length();i++){   
            if(game[i] == 'x'){
                if(holeSize) holes.push_back(holeSize);
                holeSize = 0;
                solidSize++;
            }else{
                if(solidSize) solid.push_back(solidSize);
                solidSize = 0;
                holeSize++;
            }
        }
        solid.push_back(solidSize);
        //cout << solid.size() << " " << holes.size()<<endl;
        bool notSolvable = false;
        int nowFloor = 0,nowHole = 0, endFloor = solid.size() - 1;
        int jumpCount = 0;
        while(nowFloor < endFloor){
            int jumpCharge = solid[nowFloor];
            if(jumpCharge < holes[nowFloor]) {notSolvable = true; break;}
            jumpCount++;
            jumpCharge -= holes[nowFloor];
            nowFloor++;
            // while(nowFloor<endFloor && jumpCharge >= solid[nowFloor] + holes[nowFloor]){
            //     nowFloor++;
            // }
        }

        if(notSolvable) cout << "-1" << endl;
        else cout << jumpCount << endl;


    }
    return 0;
}