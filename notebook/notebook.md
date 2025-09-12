# 📘 Notebook de Programação Competitiva

## Índice
- [Grafos](#grafos)
- [Matemática](#matemática)
- [Geometria 2D](#geometria-2d)
- [Strings](#strings)
- [Estruturas de Dados](#estruturas-de-dados)
- [Programação Dinâmica](#programação-dinâmica)

---

## Utilidades

### Header
```cpp
ios::sync_with_stdio(false);
cin.tie(nullptr);
```
### Tabela ASCII (32–126)
```
Dec Hex Char | Dec Hex Char | Dec Hex Char | Dec Hex Char
-----------------+-------------------+-------------------+----------------
32 20 (esp) | 48 30 0 | 64 40 @ | 80 50 P
33 21 ! | 49 31 1 | 65 41 A | 81 51 Q
34 22 " | 50 32 2 | 66 42 B | 82 52 R
35 23 # | 51 33 3 | 67 43 C | 83 53 S
36 24 $ | 52 34 4 | 68 44 D | 84 54 T
37 25 % | 53 35 5 | 69 45 E | 85 55 U
38 26 & | 54 36 6 | 70 46 F | 86 56 V
39 27 ' | 55 37 7 | 71 47 G | 87 57 W
40 28 ( | 56 38 8 | 72 48 H | 88 58 X
41 29 ) | 57 39 9 | 73 49 I | 89 59 Y
42 2A * | 58 3A : | 74 4A J | 90 5A Z
43 2B + | 59 3B ; | 75 4B K | 91 5B [
44 2C , | 60 3C < | 76 4C L | 92 5C
45 2D - | 61 3D = | 77 4D M | 93 5D ]
46 2E . | 62 3E > | 78 4E N | 94 5E ^
47 2F / | 63 3F ? | 79 4F O | 95 5F _
-----------------+-------------------+-------------------+----------------
96 60 ` | 112 70 p | 120 78 x |
97 61 a | 113 71 q | 121 79 y |
98 62 b | 114 72 r | 122 7A z |
99 63 c | 115 73 s | 123 7B { |
100 64 d | 116 74 t | 124 7C | |
101 65 e | 117 75 u | 125 7D } |
102 66 f | 118 76 v | 126 7E ~ |
103 67 g | 119 77 w | |
104 68 h | | |
105 69 i | | |
106 6A j | | |
107 6B k | | |
108 6C l | | |
109 6D m | | |
110 6E n | | |
111 6F o | | |
```
### Fómulas Úteis

## Grafos

### BFS
Busca em largura em **O(V+E)**.
```cpp
// BFS - O(V + E)
vector<vector<int>> adj;   // lista de adjacência

void bfs(int start) {
    queue<int> q;
    vector<bool> visited(GRAPH_MAX_SIZE, false);

    visited[start] = true;
    q.push(start);

    while (!q.empty()) {
        int u = q.front();
        q.pop();

        // Processa o vértice u aqui, se necessário

        for (int v : adj[u]) {
            if (!visited[v]) {
                visited[v] = true;
                q.push(v);
            }
        }
    }
}
```
### DFS
Busca em Profundidade em **O(V+E)**
```cpp
// DFS - O(V + E)
vector<vector<int>> adj;   // lista de adjacência
vector<bool> visited;

void dfs(int u) {
    visited[u] = true;

    // Processa o vértice u aqui, se necessário

    for (int v : adj[u]) {
        if (!visited[v]) {
            dfs(v);
        }
    }
}
```
### UNION FIND (MUDAR DPS PRA LIMPAR CADA ITERAÇÃO)
```cpp
#include <bits/stdc++.h>

using namespace std;

const int N_MAX = 100001;
int link[N_MAX];
int size[N_MAX];

// Função para encontrar o representante do conjunto
int find(int x) {
    return (x == link[x]) ? x : (link[x] = find(link[x]));
}

// Função para verificar se dois elementos estão no mesmo conjunto
bool same(int x, int y) {
    return find(x) == find(y);
}

// Função para unir dois conjuntos
void unite(int a, int b) {
    a = find(a);
    b = find(b);
    if (a == b) return;
    if (size[a] < size[b]) swap(a, b);
    size[a] += size[b];
    link[b] = a;
}
//exemplo na main
int main() {

    int N, K, i, x1, x2;
    char op;

    cin >> N >> K;

    // Inicialização da estrutura DSU
    for (i = 0; i < N; ++i) {
        link[i] = i;
        size[i] = 1;
    }

    for (i = 0; i < K; ++i) {
        cin >> op >> x1 >> x2;
        if (op == 'C') {
            if (same(x1, x2)) {
                cout << "S" << '\n';
            } else {
                cout << "N" << '\n';
            }
        } else { // 'U'
            if(!same(x1, x2))unite(x1, x2);
        }
    }

    return 0;
}
```
### DIJKSTRA
Menor caminho com pesos positivos em **O((V+E) log V)**.
```cpp
// DIJKSTRA - O((V + E) log V)
// A lista de adjacência 'adj' deve armazenar pares {vertice, peso}.
vector<int> dijkstra(int s, int n, const vector<vector<pair<int, int>>>& adj) {
    const int INF = 1e9; // Usar um valor grande como infinito
    vector<int> dist(n, INF);
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> pq;

    dist[s] = 0;
    pq.push({0, s}); // Fila de prioridade armazena {distancia, vertice}

    while (!pq.empty()) {
        auto [d, u] = pq.top();
        pq.pop();

        if (d > dist[u]) {
            continue; // Já encontramos um caminho mais curto para 'u'
        }

        for (auto [v, w] : adj[u]) { // Para cada vizinho 'v' de 'u' com peso 'w'
            if (dist[u] + w < dist[v]) {
                dist[v] = dist[u] + w;
                pq.push({dist[v], v});
            }
        }
    }
    return dist;
}
```
### Algoritmo de Floyd-Warshall (All-Pairs Shortest Path)
Encontra o caminho mais curto entre todos os pares de vértices em um grafo ponderado, usando programação dinâmica. A complexidade é **O(V^3)**, o que o torna ideal para grafos pequenos.
```cpp
#include <bits/stdc++.h>

using namespace std;

// Defina o número máximo de vértices que o problema pode ter.
const int MAXN = 101; 
// Use um valor grande para infinito, mas que evite overflow na soma.
const long long INF = 1e18; 

int n; // Número de vértices
long long dist[MAXN][MAXN];

// Função para inicializar a matriz de adjacência/distâncias
void inicializar_matriz() {
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            if (i == j) {
                dist[i][j] = 0;
            } else {
                dist[i][j] = INF;
            }
        }
    }
}

// Algoritmo de Floyd-Warshall
void floyd_warshall() {
    // Itera por cada vértice 'k' como um possível intermediário
    for (int k = 0; k < n; k++) {
        // Itera por todas as origens 'i'
        for (int i = 0; i < n; i++) {
            // Itera por todos os destinos 'j'
            for (int j = 0; j < n; j++) {
                // Se k é um intermediário válido (caminhos não infinitos)
                if (dist[i][k] != INF && dist[k][j] != INF) {
                    // Atualiza a distância se o caminho via 'k' for mais curto
                    dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]);
                }
            }
        }
    }
}

// Exemplo de uso
int main() {
    // Leitura do número de vértices (n) e arestas (m)
    int m;
    cin >> n >> m;

    inicializar_matriz();

    // Leitura das arestas
    for (int i = 0; i < m; i++) {
        int u, v;
        long long peso;
        cin >> u >> v >> peso;
        // Para grafos com arestas múltiplas, é comum pegar a de menor peso
        dist[u][v] = min(dist[u][v], peso);
        // Se o grafo for não-direcionado, adicione a aresta de volta
        // dist[v][u] = min(dist[v][u], peso);
    }

    // Roda o algoritmo
    floyd_warshall();

    // Agora, dist[i][j] contém a menor distância entre os vértices i e j.
    int origem = 0, destino = n - 1;
    if (dist[origem][destino] == INF) {
        cout << "Nao ha caminho entre " << origem << " e " << destino << endl;
    } else {
        cout << "A menor distancia entre " << origem << " e " << destino << " eh: " << dist[origem][destino] << endl;
    }
    
    // Detecção de ciclo negativo: após rodar o algoritmo, se dist[i][i] < 0
    // para qualquer 'i', então existe um ciclo negativo alcançável a partir de 'i'.

    return 0;
}
```
### Algoritmo de Bellman-Ford (Shortest Path com Pesos Negativos)
Calcula o caminho mais curto de uma única origem (source) para todos os outros vértices em um grafo ponderado. É a principal alternativa ao Dijkstra quando o grafo pode conter arestas com pesos negativos. Sua complexidade é **O(V*E)**, onde V é o número de vértices e E o de arestas.
```cpp
#include <bits/stdc++.h>

using namespace std;

// Defina o número máximo de vértices e um valor seguro para infinito.
const int MAXN = 101;
const long long INF = 1e18;

// Estrutura para representar as arestas do grafo.
// Para o Bellman-Ford, uma lista de arestas é a forma mais fácil de trabalhar.
struct Aresta {
    int u, v; // Vértices de origem e destino
    long long peso;
};

int n; // Número de vértices
vector<long long> dist(MAXN, INF);

// Algoritmo de Bellman-Ford
// Parâmetros: s (origem), arestas (vetor com todas as arestas do grafo)
// Retorna: true se NÃO houver ciclo negativo, false se houver.
// O vetor 'dist' é preenchido com as menores distâncias.
bool bellman_ford(int s, const vector<Aresta>& arestas) {
    // 1. Inicializa as distâncias
    dist.assign(n, INF);
    dist[s] = 0;

    // 2. Relaxa todas as arestas V-1 vezes
    for (int i = 0; i < n - 1; ++i) {
        for (const auto& aresta : arestas) {
            if (dist[aresta.u] != INF && dist[aresta.u] + aresta.peso < dist[aresta.v]) {
                dist[aresta.v] = dist[aresta.u] + aresta.peso;
            }
        }
    }

    // 3. V-ésima iteração para detectar ciclos de peso negativo
    for (const auto& aresta : arestas) {
        if (dist[aresta.u] != INF && dist[aresta.u] + aresta.peso < dist[aresta.v]) {
            // Se uma distância puder ser melhorada, há um ciclo negativo.
            return false;
        }
    }

    return true; // Nenhum ciclo negativo encontrado
}

// Exemplo de uso
int main() {
    int m; // Número de arestas
    cin >> n >> m;

    vector<Aresta> arestas(m);
    for (int i = 0; i < m; ++i) {
        cin >> arestas[i].u >> arestas[i].v >> arestas[i].peso;
    }

    int origem = 0;
    bool sem_ciclo_negativo = bellman_ford(origem, arestas);

    if (!sem_ciclo_negativo) {
        cout << "O grafo contem um ciclo de peso negativo!" << endl;
    } else {
        cout << "Distancias a partir da origem " << origem << ":" << endl;
        for (int i = 0; i < n; ++i) {
            if (dist[i] == INF) {
                cout << "Vertice " << i << ": Nao alcancavel" << endl;
            } else {
                cout << "Vertice " << i << ": " << dist[i] << endl;
            }
        }
    }

    return 0;
}
```
### EDMONDS-KARP
Calcula o fluxo máximo em um grafo. A complexidade é **O(V * E²)**.
```cpp
// Edmonds-Karp - O(V * E^2)
const int MAX = 110; // Número máximo de vértices
const long long INF = 1e18;

int n; // Número de vértices
long long capacity[MAX][MAX];
vector<int> adj[MAX];

// Encontra um caminho de aumento usando BFS
long long bfs(int s, int t, vector<int>& parent) {
    fill(parent.begin(), parent.end(), -1);
    parent[s] = -2;
    queue<pair<int, long long>> q;
    q.push({s, INF});

    while (!q.empty()) {
        int u = q.front().first;
        long long flow = q.front().second;
        q.pop();

        for (int v : adj[u]) {
            if (parent[v] == -1 && capacity[u][v] > 0) {
                parent[v] = u;
                long long new_flow = min(flow, capacity[u][v]);
                if (v == t) {
                    return new_flow;
                }
                q.push({v, new_flow});
            }
        }
    }
    return 0; // Nenhum caminho de aumento encontrado
}

// Função principal do Edmonds-Karp
long long edmonds_karp(int s, int t) {
    long long max_flow = 0;
    vector<int> parent(n + 1);
    long long new_flow;

    // Enquanto houver um caminho de aumento
    while ((new_flow = bfs(s, t, parent)) > 0) {
        max_flow += new_flow;
        int current = t;
        while (current != s) {
            int prev = parent[current];
            // Atualiza capacidades no grafo residual
            capacity[prev][current] -= new_flow;
            capacity[current][prev] += new_flow;
            current = prev;
        }
    }
    return max_flow;
}

// Para usar:
// 1. Defina 'n' (número de vértices).
// 2. Preencha a matriz 'capacity' e a lista 'adj'.
//    Para arestas bidirecionais, adicione capacidade em ambos os sentidos.
// 3. Chame edmonds_karp(source, sink).
// 4. Lembre-se de limpar as estruturas (capacity, adj) para múltiplos casos de teste.
```
### Componentes Fortemente Conexos (Kosaraju)
O algoritmo de Kosaraju decompõe um grafo direcionado em seus componentes fortemente conexos (SCCs). A complexidade é **O(V+E)**.
```cpp
// Componentes Fortemente Conexos (Kosaraju) - O(V + E)

// 'visitado' rastreia os vértices que já foram visitados na DFS atual.
vector<bool> visitado;

// Executa uma busca em profundidade a partir do vértice v.
// Cada vértice visitado é adicionado ao vetor 'saida' quando a DFS o deixa (pós-ordem).
void dfs(int v, const vector<vector<int>>& adj, vector<int>& saida) {
    visitado[v] = true;
    for (int u : adj[v]) {
        if (!visitado[u]) {
            dfs(u, adj, saida);
        }
    }
    saida.push_back(v);
}

// entrada: adj -- lista de adjacência do grafo G
// saida: componentes -- os componentes fortemente conexos de G
// saida: adj_condensado -- lista de adjacência do grafo de condensação G^SCC
void encontrar_sccs(const vector<vector<int>>& adj,
                    vector<vector<int>>& componentes,
                    vector<vector<int>>& adj_condensado) {
    int n = adj.size();
    componentes.clear();
    adj_condensado.clear();

    // 'ordem' será uma lista dos vértices de G ordenados pelo tempo de finalização.
    vector<int> ordem;
    visitado.assign(n, false);

    // Primeira série de buscas em profundidade no grafo original.
    for (int i = 0; i < n; i++) {
        if (!visitado[i]) {
            dfs(i, adj, ordem);
        }
    }

    // Cria a lista de adjacência do grafo transposto (G^T).
    vector<vector<int>> adj_reverso(n);
    for (int v = 0; v < n; v++) {
        for (int u : adj[v]) {
            adj_reverso[u].push_back(v);
        }
    }

    visitado.assign(n, false);
    reverse(ordem.begin(), ordem.end());

    // 'raiz_componente' indica o vértice raiz do SCC de um determinado vértice.
    vector<int> raiz_componente(n);

    // Segunda série de buscas em profundidade, no grafo transposto.
    for (int v : ordem) {
        if (!visitado[v]) {
            vector<int> componente_atual;
            dfs(v, adj_reverso, componente_atual);
            
            componentes.push_back(componente_atual);
            int raiz = componente_atual[0];
            for (int u : componente_atual) {
                raiz_componente[u] = raiz;
            }
        }
    }

    // Adiciona as arestas ao grafo de condensação.
    adj_condensado.assign(n, {});
    for (int v = 0; v < n; v++) {
        for (int u : adj[v]) {
            if (raiz_componente[v] != raiz_componente[u]) {
                adj_condensado[raiz_componente[v]].push_back(raiz_componente[u]);
            }
        }
    }
}
```
### Algoritmo de Kruskal (Minimum Spanning Tree)
A verificação de ciclos é feita de forma eficiente com uma estrutura Union-Find (DSU). A complexidade final do algoritmo é dominada pela ordenação das arestas: **O(E logE)**.
```cpp
#include <bits/stdc++.h>

using namespace std;

// Estrutura para representar uma aresta ponderada
struct Aresta {
    int u, v, peso;

    // Operador para permitir a ordenação das arestas pelo peso
    bool operator<(const Aresta& other) const {
        return peso < other.peso;
    }
};

// --- Estrutura Union-Find (DSU) ---
vector<int> pai;
vector<int> tamanho;

// Encontra o representante do conjunto de 'i' com compressão de caminho
int find(int i) {
    if (pai[i] == i) {
        return i;
    }
    return pai[i] = find(pai[i]);
}

// Une os conjuntos de 'a' e 'b' por tamanho
void unite(int a, int b) {
    a = find(a);
    b = find(b);
    if (a != b) {
        if (tamanho[a] < tamanho[b]) {
            swap(a, b);
        }
        pai[b] = a;
        tamanho[a] += tamanho[b];
    }
}
// --- Fim da Estrutura Union-Find ---


// Função principal do Algoritmo de Kruskal
long long kruskal(int n, vector<Aresta>& arestas) {
    // Inicializa a estrutura Union-Find
    pai.resize(n);
    iota(pai.begin(), pai.end(), 0); // Preenche pai[i] = i
    tamanho.assign(n, 1);

    // 1. Ordena todas as arestas pelo peso
    sort(arestas.begin(), arestas.end());

    long long custo_total = 0;
    vector<Aresta> mst_arestas;

    // 2. Percorre as arestas ordenadas
    for (const auto& aresta : arestas) {
        // 3. Verifica se os vértices da aresta estão em componentes diferentes
        if (find(aresta.u) != find(aresta.v)) {
            // Se sim, a aresta não forma um ciclo
            custo_total += aresta.peso;
            mst_arestas.push_back(aresta);
            unite(aresta.u, aresta.v);
        }
    }

    // Opcional: Verificar se uma MST foi formada (todos os vértices conectados)
    // if (mst_arestas.size() != n - 1) {
    //     return -1; // Grafo não é conexo
    // }

    return custo_total;
}
```

## Matemática

### MDC - Máximo Divisor Comum (GCD)
O Algoritmo de Euclides é o método mais eficiente para encontrar o maior divisor comum entre dois números. A complexidade é **O(log(min(a,b)))**.
```cpp
// MDC - Algoritmo de Euclides - O(log(min(a, b)))
int gcd(int a, int b) {
    while (b) {
        a %= b;
        // Troca os valores de a e b
        int temp = a;
        a = b;
        b = temp;
    }
    return a;
}
```
### MMC - Mínimo Múltiplo Comum (LCM)
```cpp
int lmc(int m, int n){
    return (m * n) / gcd(m, n);
}
```
### Conversão de Bases Numéricas
#### De Decimal (Base 10) para Base B
Usa o método de divisões sucessivas. O resultado é uma string, pois pode conter caracteres (ex: 'A', 'F' para hexadecimal).
```cpp
#include <bits/stdc++.h>

using namespace std;

// Converte um número 'n' da base 10 para uma base 'b' (2 <= b <= 36).
string from_decimal(long long n, int b) {
    if (n == 0) {
        return "0";
    }
    
    string result = "";
    while (n > 0) {
        int remainder = n % b;
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
```
#### De Base B para Decimal (Base 10)
```cpp
#include <bits/stdc++.h>

using namespace std;

// Converte uma string 'num' na base 'b' para a base 10 (decimal).
long long to_decimal(const string& num, int b) {
    long long result = 0;
    long long power = 1;

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
```
### CRIVO DE ERATÓSTENES
É um algoritmo altamente eficiente para encontrar todos os números primos até um determinado limite N. Sua complexidade de tempo é **O(N log logN)**
```cpp
#include <bits/stdc++.h>

using namespace std;

// Define o limite máximo para o crivo.
// Em problemas, ajuste para o maior valor necessário.
const int MAXN = 1000001; 

// Vetor booleano global para armazenar a primalidade.
// is_prime[i] = true se i for primo, false caso contrário.
vector<bool> is_prime(MAXN, true);

// Função que implementa o Crivo de Eratóstenes.
// Preenche o vetor is_prime em O(N log log N).
void sieve() {
    // 1. Marcar 0 e 1 como não-primos
    is_prime[0] = is_prime[1] = false;

    // 2. Iterar a partir de p=2
    // A iteração vai até p*p < MAXN, pois qualquer número composto
    // n terá um fator primo <= sqrt(n).
    for (int p = 2; p * p < MAXN; p++) {
        // 3. Se p ainda não foi marcado, ele é primo
        if (is_prime[p]) {
            // 4. Marca todos os múltiplos de p como não-primos
            // Otimização: começamos a marcar de p*p, pois os múltiplos
            // menores (2*p, 3*p, etc.) já foram marcados por primos menores.
            for (int i = p * p; i < MAXN; i += p) {
                is_prime[i] = false;
            }
        }
    }
}

// Exemplo de uso
int main() {
    // Pré-computa todos os primos até MAXN.
    // Chame esta função uma vez no início do seu código.
    sieve();

    // Agora, verificar se um número é primo é uma consulta O(1).
    cout << "37 eh primo? " << (is_prime[37] ? "Sim" : "Nao") << endl;
    cout << "100 eh primo? " << (is_prime[100] ? "Sim" : "Nao") << endl;

    // O código da imagem lia A e B e contava os primos no intervalo.
    // Com o crivo, isso se torna trivial:
    int A = 1, B = 100;
    int count = 0;
    for (int i = A; i <= B; ++i) {
        if (is_prime[i]) {
            count++;
        }
    }
    cout << "Existem " << count << " primos entre " << A << " e " << B << "." << endl;

    return 0;
}
```
### Encontrar Todos os Divisores
Para encontrar todos os divisores de um número N, podemos iterar de 1 até sqrtN. Se i divide N, então N/i também é um divisor. Essa abordagem tem complexidade **O(sqrtN)**
```cpp
#include <bits/stdc++.h>

using namespace std;

// Encontra todos os divisores de 'n' em O(sqrt(n)).
vector<long long> encontrar_divisores(long long n) {
    vector<long long> divisores;
    for (long long i = 1; i * i <= n; ++i) {
        if (n % i == 0) {
            divisores.push_back(i);
            // Evita adicionar a raiz quadrada duas vezes se 'n' for um quadrado perfeito.
            if (i * i != n) {
                divisores.push_back(n / i);
            }
        }
    }
    // Opcional: ordena os divisores para uma saída mais limpa.
    sort(divisores.begin(), divisores.end());
    return divisores;
}
```
### FIBONACCI
Fibonacci iterativo (para n pequenos)
```cpp
long long fib_iterativo(int n) {
    if (n <= 1) {
        return n;
    }
    long long a = 0, b = 1, c;
    for (int i = 2; i <= n; i++) {
        c = a + b;
        a = b;
        b = c;
    }
    return b;
}
```
Fibonacci com Exponenciação de Matriz (para n grandes como 10^18)
```cpp
#include <vector>

// Fibonacci com Exponenciação de Matriz - O(log n)
// Ideal para N grande e com resultado modular.

// Define um tipo 'matrix' para facilitar a leitura do código.
using matrix = std::vector<std::vector<long long>>;

// Define o módulo para os cálculos. Mude se o problema pedir outro.
const int MOD = 1e9 + 7;

// Função para multiplicar duas matrizes 2x2 sob um módulo.
matrix multiply(const matrix& A, const matrix& B) {
    matrix C = {{0, 0}, {0, 0}};
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            for (int k = 0; k < 2; k++) {
                C[i][j] = (C[i][j] + A[i][k] * B[k][j]) % MOD;
            }
        }
    }
    return C;
}

// Função para elevar uma matriz a uma potência (exponenciação rápida).
matrix matrix_pow(matrix A, long long p) {
    matrix res = {{1, 0}, {0, 1}}; // Matriz identidade

    while (p > 0) {
        if (p & 1) { // Se p for ímpar
            res = multiply(res, A);
        }
        A = multiply(A, A);
        p >>= 1; // p = p / 2
    }
    return res;
}

// Função principal para encontrar o N-ésimo número de Fibonacci.
long long fib(long long n) {
    if (n == 0) {
        return 0;
    }

    // Matriz de transformação de Fibonacci.
    matrix T = {{1, 1}, {1, 0}};
    
    // Calcula T^n. De acordo com a fórmula, o resultado F(n)
    // estará na posição [0][1] da matriz resultante.
    T = matrix_pow(T, n);
    
    return T[0][1];
}

/*
// Exemplo de uso na main:
int main() {
    long long n;
    std::cin >> n;
    std::cout << fib(n) << std::endl;
    return 0;
}
*/
```
### FAST POW
Exponenciação Rápida (Binária)
Calcula (a^b)%m de forma eficiente. A complexidade é **O(logb)**.

Esta é a versão modular, ideal para problemas que pedem o resultado sob um módulo (como 10^9 +7) para evitar que os números fiquem grandes demais (overflow). Se um problema pedir apenas o cálculo de a^b e o resultado couber em um long long, basta adaptar a função removendo o parâmetro m e todas as operações de módulo (%).
```cpp
// Exponenciação Rápida (Binária) - O(log b)
// Versão para cálculo modular: (a^b) % m
long long binpow(long long a, long long b, long long m) {
    // A linha abaixo é importante caso 'a' seja maior que 'm'.
    // Se o problema pedir um módulo, é sempre bom garantir
    // que os números manipulados permaneçam pequenos.
    a %= m;
    
    long long res = 1;
    while (b > 0) {
        // Se o bit menos significativo de b for 1 (ou seja, b é ímpar)
        if (b & 1)
            // Multiplica o resultado por 'a' e aplica o módulo
            // para manter o número dentro do limite.
            res = (res * a) % m;
        
        // Eleva 'a' ao quadrado e aplica o módulo.
        // Isso evita que 'a' cresça excessivamente.
        a = (a * a) % m;
        
        b >>= 1; // b = b / 2
    }
    return res;
}

```

## Geometria 2D

### Template Básico para Geometria 2D
Este template define uma estrutura point para representar pontos ou vetores em um plano 2D e inclui as operações geométricas mais comuns. A precisão de ponto flutuante é tratada com uma constante EPS.
```cpp
#include <bits/stdc++.h>
#define REP(i,n) for(int i=0;i<(int)n;++i)
#define EACH(i,c) for(__typeof((c).begin()) i=(c).begin(); i!=(c).end(); ++i)
#define ALL(c) (c).begin(), (c).end()
#define SIZE(x) (int((x).size()))
#define MAXSZ 1000

using namespace std;

const int INF = 0x3F3F3F3F;
const double PI = 2*acos(0);
const double EPS = 1e-10;

/*
 * Função de Comparação de 2 valores
 *
 * Parametros:
 * double x;
 * double y;
 *
 * Retorna:
 * -1 se x < y
 * 0 se x == y
 * 1 se x > y
 */
inline int cmp(double x, double y=0, double tol=EPS)
{
    return (x<=y+tol) ? (x+tol<y) ? -1 : 0 : 1;
}

/* Estrutura de dados para pontos */

struct point
{
    double x, y;

    point(double x = 0, double y = 0): x(x), y(y) {}

    point operator +(point q) { return point(x + q.x, y + q.y); } 
    point operator -(point q) { return point(x - q.x, y - q.y); }
    point operator *(double t) { return point(x * t, y * t); }
    point operator /(double t) { return point(x / t, y / t); }
    double operator *(point q) { return x * q.x + y * q.y; } // produto escalar
    double operator %(point q) { return x * q.y - y * q.x; } // produto vetorial

    int cmp(point q) const {
        if (int t = ::cmp(x, q.x)) return t;
        return ::cmp(y, q.y);
    }

    bool operator ==(point q) const { return cmp(q) == 0; }
    bool operator !=(point q) const { return cmp(q) != 0; }
    bool operator <(point q) const { return cmp(q) < 0; }
    bool operator >(point q) const { return cmp(q) > 0; }
    bool operator <=(point q) const { return cmp(q) <= 0; }
    bool operator >=(point q) const { return cmp(q) >= 0; }

    friend ostream& operator <<(ostream& o, point p) {
        return o << "(" << p.x << ", " << p.y << ")";
    }

    static point pivot;
};

point point::pivot;

// Retorna a magnitude (comprimento) de um vetor
double abs(point p) { return hypot(p.x, p.y); }
// Retorna o ângulo do vetor em radianos com o eixo X
double arg(point p) { return atan2(p.y, p.x); }

typedef vector<point> polygon;
typedef pair<point, double> circle;

int ccw(point p, point q, point r)
{
    return cmp((p - r) % (q - r));
    // +1: q está à esquerda do segmento rp
    // -1: q está à direita do segmento rp
    // 0: Os três pontos são colineares (estão na mesma linha).
}
```
### Ângulo Entre Dois Vetores / Segmentos
```cpp
// Pré-requisito: Template Básico de Geometria 2D

// Calcula o ângulo PQR (com vértice em Q) em radianos.
double angulo(point p, point q, point r) {
    // Cria os vetores a partir do vértice Q
    point u = p - q; // Vetor QP
    point v = r - q; // Vetor QR

    // Usa os operadores sobrecarregados:
    // u % v -> produto vetorial (cross product)
    // u * v -> produto escalar (dot product)
    return atan2(u % v, u * v);
}
// para graus: double graus = angulo_radianos * 180.0 / PI;
```
### Template Básico para Geometria 2D (Gemini)
Este template define uma estrutura point para representar pontos ou vetores em um plano 2D e inclui as operações geométricas mais comuns. A precisão de ponto flutuante é tratada com uma constante EPS.
```cpp
#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>

using namespace std;

const double EPS = 1e-9;

// Retorna -1 se x < 0, 0 se x == 0, 1 se x > 0
int sgn(double x) {
    return (x > EPS) - (x < -EPS);
}

struct point {
    double x, y;

    // Construtores
    point() : x(0), y(0) {}
    point(double x, double y) : x(x), y(y) {}

    // Operadores
    point operator+(const point& o) const { return point(x + o.x, y + o.y); }
    point operator-(const point& o) const { return point(x - o.x, y - o.y); }
    point operator*(double s) const { return point(x * s, y * s); }
    point operator/(double s) const { return point(x / s, y / s); }

    // Comparações (considerando EPS)
    bool operator==(const point& o) const {
        return sgn(x - o.x) == 0 && sgn(y - o.y) == 0;
    }
    bool operator<(const point& o) const {
        if (sgn(x - o.x) != 0) return x < o.x;
        return y < o.y;
    }

    // Métodos
    double norm_sq() const { return x * x + y * y; }
    double norm() const { return sqrt(norm_sq()); }
    point unit() const { return *this / norm(); }
};

// Produto escalar
double dot(point p, point q) {
    return p.x * q.x + p.y * q.y;
}

// Produto vetorial (2D)
double cross(point p, point q) {
    return p.x * q.y - p.y * q.x;
}

// Distância euclidiana entre dois pontos
double dist(point p, point q) {
    return (p - q).norm();
}

// Área de um triângulo a partir de seus vértices
double area(point p, point q, point r) {
    return fabs(cross(q - p, r - p)) / 2.0;
}

// Define um polígono como um vetor de pontos
typedef vector<point> polygon;

// Área de um polígono (fórmula de Shoelace)
// A área é positiva se os vértices estiverem em sentido anti-horário, negativa caso contrário.
double signed_area(const polygon& p) {
    double area = 0;
    int n = p.size();
    for (int i = 0; i < n; i++) {
        area += cross(p[i], p[(i + 1) % n]);
    }
    return area / 2.0;
}

// Verifica se um ponto está dentro de um polígono (algoritmo do número de enrolamento)
// Funciona para polígonos simples (não auto-intersecantes).
bool is_inside(const polygon& P, point p) {
    double angle = 0;
    int n = P.size();
    for(int i = 0; i < n; i++) {
        point p1 = P[i], p2 = P[(i + 1) % n];
        angle += atan2(cross(p1 - p, p2 - p), dot(p1 - p, p2 - p));
    }
    return sgn(angle) != 0;
}
```

## Strings

### String Hashing
O hashing polinomial é uma técnica poderosa para converter strings em números (hashes), permitindo comparações em tempo O(1). A complexidade para calcular os hashes de todos os prefixos de uma string de tamanho n é **O(n)**.
```cpp
// String Hashing - O(n)
// Calcula o hash de uma string inteira
long long compute_hash(const string& s) {
    const int p = 5647; // Número primo, aprox. o tamanho do alfabeto
    const int m = 1e9 + 9; // Módulo grande
    //outro modulo possivel: 1e9 + 7, outra base possivel: 4079
    long long hash_value = 0;
    long long p_pow = 1;
    for (char c : s) {
        hash_value = (hash_value + (c - 'a' + 1) * p_pow) % m;
        p_pow = (p_pow * p) % m;
    }
    return hash_value;
}
```
### Rabin-Karp (Busca de Padrão)
Utiliza hashing para encontrar todas as ocorrências de um padrão s em um texto t. A complexidade média é **O(|s| + |t|)**, mas pode degradar para **O(|s| * |t|)** em casos de muitas colisões de hash.
```cpp
// Rabin-Karp - O(|s| + |t|)
vector<int> rabin_karp(const string& s, const string& t) {
    const int p = 31;
    const int m = 1e9 + 9;
    int S = s.length(), T = t.length();

    // Pré-calcula potências de p
    vector<long long> p_pow(max(S, T));
    p_pow[0] = 1;
    for (int i = 1; i < p_pow.size(); i++) {
        p_pow[i] = (p_pow[i - 1] * p) % m;
    }

    // Calcula hashes de todos os prefixos do texto 't'
    vector<long long> h(T + 1, 0);
    for (int i = 0; i < T; i++) {
        h[i + 1] = (h[i] + (t[i] - 'a' + 1) * p_pow[i]) % m;
    }

    // Calcula o hash do padrão 's'
    long long h_s = 0;
    for (int i = 0; i < S; i++) {
        h_s = (h_s + (s[i] - 'a' + 1) * p_pow[i]) % m;
    }

    vector<int> occurrences;
    for (int i = 0; i + S - 1 < T; i++) {
        // Calcula o hash da substring atual de 't'
        long long cur_h = (h[i + S] - h[i] + m) % m;
        
        // Compara com o hash do padrão
        if (cur_h == (h_s * p_pow[i]) % m) {
            occurrences.push_back(i);
        }
    }
    return occurrences;
}
```
### Knuth-Morris-Pratt (KMP)
Um algoritmo de busca de padrão extremamente eficiente com complexidade **O(|s| + |t|)** no pior caso.
#### Função de Prefixo (LPS Array)
Primeiro, calculamos um array pi (também conhecido como LPS - Longest Proper Prefix which is also Suffix). pi[i] armazena o tamanho do maior prefixo próprio da string s[0...i] que também é um sufixo dessa mesma string.
```cpp
// KMP - Função de Prefixo - O(|s|)
vector<int> prefix_function(const string& s) {
    int n = s.length();
    vector<int> pi(n);
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        while (j > 0 && s[i] != s[j]) {
            j = pi[j - 1];
        }
        if (s[i] == s[j]) {
            j++;
        }
        pi[i] = j;
    }
    return pi;
}
```
#### KMP (Busca de Padrão)
Com o array pi pré-calculado, o algoritmo percorre o texto e o padrão sem precisar retroceder no texto, garantindo a eficiência.
```cpp
// KMP - Algoritmo Principal - O(|t|)
vector<int> kmp(const string& t, const string& s) {
    vector<int> pi = prefix_function(s);
    vector<int> match;
    for (int i = 0, j = 0; i < t.length(); i++) {
        while (j > 0 && t[i] != s[j]) {
            j = pi[j - 1];
        }
        if (t[i] == s[j]) {
            j++;
        }
        if (j == s.length()) {
            match.push_back(i - j + 1);
            j = pi[j - 1]; // Continua a busca por mais ocorrências
        }
    }
    return match;
}
```

## Estruturas de Dados

### Sliding Window Maximum (Janela Deslizante)
```cpp
#include <bits/stdc++.h>

using namespace std;

// Sliding Window Maximum - O(n)
// Encontra o valor máximo em cada janela de tamanho 'k'.
// Retorna um vetor contendo o máximo de cada janela.
// O vetor de resultado terá `arr.size() - k + 1` elementos.

vector<int> sliding_window_max(const vector<int>& arr, int k) {
    int n = arr.size();
    vector<int> result;
    // O deque armazena pares {valor, índice} dos elementos da janela.
    deque<pair<int, int>> dq;

    for (int i = 0; i < n; ++i) {
        // 1. Remove da frente o elemento que já saiu da janela.
        // A janela atual tem os índices [i - k + 1, i].
        if (!dq.empty() && dq.front().second <= i - k) {
            dq.pop_front();
        }

        // 2. Remove da traseira os elementos menores ou iguais ao atual,
        // pois eles nunca poderão ser o máximo enquanto o elemento atual
        // estiver na janela.
        while (!dq.empty() && dq.back().first <= arr[i]) {
            dq.pop_back();
        }

        // 3. Adiciona o elemento atual {valor, índice} na traseira.
        dq.push_back({arr[i], i});

        // 4. Se a janela já está completa, o máximo é o da frente.
        // A primeira janela completa termina no índice k-1.
        if (i >= k - 1) {
            result.push_back(dq.front().first);
        }
    }
    return result;
}
```

## Programação Dinâmica

### Ouaaa cade as DP?









