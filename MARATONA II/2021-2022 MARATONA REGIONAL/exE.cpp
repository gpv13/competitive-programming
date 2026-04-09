#include<bits/stdc++.h>
using namespace std;
int main(){

    int n;
    cin >> n;
    vector<int> list0;
    vector<int> list1;
    int start = 2, temp = 0;
    for(int i=0; i<n;i++){
        int num, aux;
        cin >> num >> aux;
        if(aux){
            list1.push_back(num);
        }else{
            list0.push_back(num);
        }
        if(start == 2){
            start = aux;
        }
    }

    int p1 = 0, p0 = 0;
    // temp+= (start) ? list1[p1++] : list0[p0++];
    // int tempoUltimo = temp;

    while(p1 < list1.size() || p0 < list0.size()){

        int maiorTemp = -1;
        bool acabouDeComecar = true;
        if(start){
            while(p1 < list1.size() && (list1[p1] <= maiorTemp+10 || acabouDeComecar)){

                if(list1[p1] < temp) list1[p1] = temp;
                // tempoUltimo = min(temp,list1[p1]);
                // temp = tempoUltimo + 10;
                maiorTemp = max(maiorTemp, list1[p1]);
                acabouDeComecar = false;
                p1++;
            }
            temp = maiorTemp + 10;
        }else{
            while(p0 < list0.size() && (list0[p0] <= maiorTemp+10 || acabouDeComecar)){

                if(list0[p0] < temp) list0[p0] = temp;

                // tempoUltimo = min(temp, list0[p0]);
                // temp = tempoUltimo + 10;
                maiorTemp = max(maiorTemp, list0[p0]);
                acabouDeComecar = false; 
                p0++;
            }
            temp = maiorTemp + 10;
        }
        // cout  << temp << endl;

        if(p0 >= list0.size()) start = 1;
        else if(p1 >= list1.size()) start = 0;
        else{
            start = (list0[p0] < list1[p1]) ? 0 : 1;
        }

    }
    cout << temp << endl;
    return 0;
}