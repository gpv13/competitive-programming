#include <bits/stdc++.h>

using namespace std;

unsigned long long to_decimal(const string& num, int b) {
    unsigned long long result = 0;
    unsigned long long power = 1;

    // Itera pela string da direita para a esquerda.
    for (int i = num.length() - 1; i >= 0; i--) {
        int digit_value;
        if (num[i] >= '0' && num[i] <= '9') {
            digit_value = num[i] - '0';
        } else {
            digit_value = num[i] - 'A' + 10;
        }

        if (digit_value >= b) {
            // Dígito inválido para a base fornecida.
            // Você pode tratar o erro aqui (ex: retornar -1).
            return -1; 
        }

        result += digit_value * power;
        power *= b;
    }
    return result;
}


// Converte um número 'n' da base 10 para uma base 'b' (2 <= b <= 36).
string from_decimal(unsigned long long n, int b) {
    if (n == 0) {
        return "0";
    }
    
    string result = "";
    while (n > 0) {
        unsigned long long int remainder = n % b;
        if (remainder < 10) {
            // Converte o resto numérico para seu caractere '0'-'9'
            result += to_string(remainder);
        } else {
            // Converte o resto numérico para seu caractere 'A'-'Z'
            result += (char)('A' + (remainder - 10));
        }
        n /= b;
    }
    
    // Os restos foram coletados na ordem inversa, então revertemos a string.
    reverse(result.begin(), result.end());
    return result;
}


// Função para subtrair 1 de uma string binária
std::string subtractOne(std::string bin) {
    // Caso especial: se o número for "0", não há o que subtrair (em contexto não-negativo)
    if (bin == "0" || bin.empty()) {
        return "-1"; // Ou pode retornar "0" ou lançar um erro, dependendo do requisito
    }

    int n = bin.length();

    // Percorre a string da direita para a esquerda
    for (int i = n - 1; i >= 0; --i) {
        if (bin[i] == '1') {
            // Encontrou um '1', troca para '0' e termina
            bin[i] = '0';
            
            // Remove zeros à esquerda, se houver
            size_t first_one = bin.find_first_of('1');
            if (std::string::npos == first_one) {
                // Se não encontrou nenhum '1', o resultado é "0" (caso de "1" - 1)
                return "0";
            }
            return bin.substr(first_one);

        } else { // bin[i] == '0'
            // Encontrou um '0', troca para '1' e continua o "empréstimo"
            bin[i] = '1';
        }
    }
    
    // Se o loop terminar sem retornar, significa que a entrada era algo como "000",
    // o que é um caso inválido se assumirmos que não há zeros à esquerda.
    // Mas a lógica acima já cobre o caso de "1", "10", etc.
    // Esta linha normalmente não será atingida com entradas válidas.
    return bin; 
}


bool ehPal(string pal){

    string aux = pal;
    reverse(pal.begin(), pal.end());
    if(aux == pal) return true;
    else return false;

}

string proximoPal(string dec){
    while(!ehPal(dec) && dec != "0"){
        dec = subtractOne(dec);
    }
    return dec;
}

int main(){

    unsigned long long int num;
    cin >> num;
    string decimal;
    decimal = from_decimal(num, 2);
    string result = proximoPal(decimal);
    unsigned long long int resp = to_decimal(result, 2);
    cout << resp << endl;

    return 0;
}