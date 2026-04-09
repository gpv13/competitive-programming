#include <iostream>
#include <vector>
#include <deque>
#include <algorithm>
#include <climits>

using namespace std;

int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    int c, n;
    cin >> c >> n;

    vector<int> temps(n);
    for (int i = 0; i < n; ++i) {
        cin >> temps[i];
    }

    deque<pair<int, int>> window_max_deque;

    int min_of_maxes = INT_MAX;

    for (int i = 0; i < n; ++i) {
        
        if (!window_max_deque.empty() && window_max_deque.front().second <= i - (c + 1)) {
            window_max_deque.pop_front();
        }

        while (!window_max_deque.empty() && window_max_deque.back().first <= temps[i]) {
            window_max_deque.pop_back();
        }

        window_max_deque.push_back({temps[i], i});

        if (i >= c) {
            int max_in_current_window = window_max_deque.front().first;
            min_of_maxes = min(min_of_maxes, max_in_current_window);
        }
    }

    cout << min_of_maxes << endl;

    return 0;
}