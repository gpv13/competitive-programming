#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;

    cin >> n;

    for(int i=0;i<n;i++){
        int w, h, a, b;
        int x1, y1, x2, y2;
        cin >> w >> h >> a >> b;
        cin >> x1 >> y1 >> x2 >> y2;
        
        if((x1 == x2 && (y1-y2)%b !=0)||( y1 == y2 && (x1-x2)%a != 0)){
            cout << "No" << endl;
        }
        else if((x1-x2)%a !=0 && (y1-y2)%b != 0){
            cout << "No" << endl;
        }
        else cout << "Yes" << endl;

    }



    return 0;
}