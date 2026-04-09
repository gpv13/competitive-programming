#include<bits/stdc++.h>
using namespace std;
int main(){



    int t;
    cin >> t;

    int nimber[32][32];

    memset(nimber, 0, sizeof(nimber));

    int opsx[] = {-2, -2, 1, -1};
    int opsy[] = {1, -1, -2, -2};

    for(int i=0;i<=30;i++){

        int x = 0;
        int y = i;
        for(int j=0;j<=i;j++){

            set<int> has_ocurred;

            for(int k = 0;k<4;k++){
                if(x + opsx[k] >= 0 && x + opsx[k] < 15 && y + opsy[k] >= 0 && y + opsy[k] < 15){
                    has_ocurred.insert(nimber[x+opsx[k]][y+opsy[k]]);
                }
            }

            int mex = 0;
            while(has_ocurred.count(mex)) mex++;

            nimber[x][y] = mex;

            x++;
            y--;

        }

    }

    // for(int i =0;i<15;i++){
    //     for(int j=0;j<15;j++){
    //         cout << "[" << nimber[i][j] << "]";
    //     }
    //     cout << endl;
    // }

    while(t--){
        int n;
        cin >> n;
        int xr = 0;
        for(int i=0;i<n;i++){

            int x, y;
            cin >> x >> y;
            x--; y--;
            xr ^= nimber[x][y];
        }
        if(xr) cout << "First" << endl;
        else cout << "Second" << endl;
    }

    

    return 0;
}