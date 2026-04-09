#include<bits/stdc++.h>
using namespace std;

int main(){
    
    int y, n;
    vector<int> slots;
    cin >> y >> n;
    for(int i=0;i<y;i++){
        int aux;
        cin >> aux;
        slots.push_back(aux);
    }
    int a, p, f;
    for(int i=0;i<n;i++){
        int sad = 0;
        cin >> a >> p >> f;
        if(slots[a-1] >= p){
            cout << "0" << endl;
        }else{
            for(int j=a-1;j<a+f;j++){
                if(slots[j] >= p){
                    sad++;
                }
            }
            cout << sad << endl;
        }
    }

    return 0;
}