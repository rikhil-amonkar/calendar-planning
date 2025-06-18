from collections import deque

graph = {
    'V': [('B', 3, 350), ('I', 4, 180), ('M', 2, 200), ('S', 1, 100)],
    'B': [('V', 4, 420), ('H', 2, 180), ('C', 3, 240), ('P', 4, 310)],
    'I': [('V', 4, 180), ('M', 3, 160), ('S', 2, 80), ('T', 5, 220)],
    'M': [('V', 2, 200), ('I', 3, 160), ('S', 2, 120), ('R', 6, 380)],
    'S': [('V', 1, 100), ('I', 2, 80), ('M', 2, 120)],
    'P': [('B', 4, 310), ('V', 3, 290)],
    'R': [('M', 6, 380), ('T', 3, 200)],
    'H': [('B', 2, 180), ('C', 1, 100)],
    'C': [('B', 3, 240), ('H', 1, 100)],
    'T': [('I', 5, 220), ('R', 3, 200)]
}

cities = ['V','B','I','M','S','P','R','H','C','T']
city_to_index = {city: idx for idx, city in enumerate(cities)}
n = len(cities)
all_visited = (1 << n) - 1

city_names = {
    'V': 'Vienna',
    'B': 'Budapest',
    'I': 'Innsbruck',
    'M': 'Munich',
    'S': 'Salzburg',
    'P': 'Prague',
    'R': 'Rogensburg',
    'H': 'Hallstatt',
    'C': 'Cologne',
    'T': 'Trier'
}

def main():
    visited = set()
    queue = deque()
    start_mask = 1 << city_to_index['V']
    start_state = ('V', start_mask, 0)
    visited.add(start_state)
    queue.append(start_state)
    parent = {start_state: (None, None)}
    found_state = None
    s_end_final = 0

    while queue:
        state = queue.popleft()
        city, mask, day = state

        if city == 'V' and mask == all_visited:
            s_end = 29 - day
            if 1 <= s_end <= 5:
                found_state = state
                s_end_final = s_end
                break

        for s in range(1, 6):
            leave_day = day + s
            if leave_day > 28:
                break
            for neighbor, travel_time, _ in graph[city]:
                new_day = leave_day + travel_time
                if new_day > 28:
                    continue
                nidx = city_to_index[neighbor]
                new_mask = mask | (1 << nidx)
                new_state = (neighbor, new_mask, new_day)
                if new_state not in visited:
                    visited.add(new_state)
                    queue.append(new_state)
                    parent[new_state] = (state, s)

    if found_state is None:
        print("No solution found")
    else:
        seq = []
        seq.append(('V', s_end_final))
        current_state = found_state
        while parent[current_state] != (None, None):
            prev_state, stay_duration = parent[current_state]
            seq.append((prev_state[0], stay_duration))
            current_state = prev_state

        total_days = {city: 0 for city in cities}
        for city_letter, stay in seq:
            total_days[city_letter] += stay

        result = []
        for city in cities:
            result.append((city_names[city], total_days[city]))
        
        print(result)

if __name__ == '__main__':
    main()