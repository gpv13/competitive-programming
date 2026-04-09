#include <bits/stdc++.h>
using namespace std;

int main() {

    int pontos[2];
    int games[2];

    memset(pontos, 0, sizeof pontos);
    memset(games, 0, sizeof games);

    bool acabou = false;
    int atual = 0;

    string jogo;
    cin >> jogo;

    for(int i = 0; i < jogo.size(); i++) {

        if(jogo[i] == 'S') {
            pontos[atual]++;
            if((pontos[atual] >= 5 && (pontos[atual] - pontos[atual ^ 1]) >= 2) || pontos[atual] == 10) {
                pontos[atual] = 0;
                pontos[atual ^ 1] = 0;
                games[atual]++;
                if(games[atual] == 2) {
                    acabou = true;
                }
            }
        }
        else if(jogo[i] == 'R') {
            atual ^= 1;
            pontos[atual]++;
            if((pontos[atual] >= 5 && (pontos[atual] - pontos[atual ^ 1]) >= 2) || pontos[atual] == 10) {
                pontos[atual] = 0;
                pontos[atual ^ 1] = 0;
                games[atual]++;
                if(games[atual] == 2) {
                    acabou = true;
                }
            }
        }
        else if(jogo[i] == 'Q') {
            if(acabou) {
                if(games[0] == 2) {
                    cout << "2 (winner) - " << games[1] << endl;
                }
                else {
                    cout << games[0] << " - 2 (winner)" << endl;
                }
            }
            else {
                if(atual == 0) {
                    cout << games[0] << " (" << pontos[0] << "*) - " << games[1] << " (" << pontos[1] << ")" << endl;  
                }
                else {
                    cout << games[0] << " (" << pontos[0] << ") - " << games[1] << " (" << pontos[1] << "*)" << endl; 
                }
            }
        }

    }


    return 0;
}