#include<bits/stdc++.h>
using namespace std;

long long int estaEsq(pair<long long int,long long int> a, pair<long long int,long long int> b, pair<long long int,long long int> c){
    return(((b.first - a.first)*(c.second-a.second) - (b.second - a.second)*(c.first - a.first)));
}

int main(){

    long long int n;
    cin >> n;
    vector<pair<long long int,long long int>> points(n);
    for(long long int i=0;i<n;i++){
        long long int x, y;
        cin >> x >> y;
        points[i] = {x,y};
    }
    pair<long long int,long long int> camera;
    cin >> camera.first >> camera.second;
    int sinalIni = 0;
    bool deuRuim = false;
    for(long long int i=0;i<n;i++){

        pair<long long int,long long int> a, b;
        if(!i){
            b = points[n-1];
        }else{
            b = points[i-1];
        }
        a = points[i];

        long long sentido = estaEsq(a,b,camera);
        if(!i) sinalIni = sentido;
        else{
            if((sinalIni < 0 && sentido > 0) || (sinalIni > 0 && sentido < 0)){
                deuRuim = true;
                break;
            }
        }
        if(sentido == 0 || sinalIni == 0){
            deuRuim = true;
            break;
        }
    }

    
    if(deuRuim){
        cout << "N" << endl;
    }else{
        cout << "S" << endl;
    }

    return 0;
}