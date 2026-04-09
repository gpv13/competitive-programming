#include <bits/stdc++.h>
using namespace std;

int main() {

    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    
    int n, w, h, s;
    cin >> n >> w >> h>> s;
    pair<char, int> melhorCombo = {'.', -1};
    for(int k=0;k<n;k++){
        char c;
        cin >> c;
        int melhorLinha = -1;
        for(int i=0;i<h;i++){
            int contaPisca = 0;
            string linha;
            cin >> linha;
            for(int j=0;j<w;j++){

                if(j==w-1 && linha[j] == '#') {contaPisca++;}
                if(!j && linha[j] == '#') {contaPisca++;}
                else if(j && linha[j] == '#' && linha[j-1] != '#') {contaPisca++;}
                else if(j && linha[j] == '.' && linha[j-1] != '.') {contaPisca++;}
            }
            melhorLinha = max(melhorLinha, contaPisca);
        }
        if(melhorLinha > melhorCombo.second){
            melhorCombo.first = c;
            melhorCombo.second = melhorLinha;
        }
    }

    // cout << melhorCombo.second << endl;
    int quant = ceil((double)s/(double)melhorCombo.second);

    for(int i=0;i<quant;i++) cout << melhorCombo.first;
    cout << endl;

    return 0;
}