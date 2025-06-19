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

def main():
    visited = set()
    parent = {}
    queue = deque()
    start_state = ('V', 1 << city_to_index['V'], 0)
    visited.add(start_state)
    queue.append(start_state)
    parent[start_state] = (None, None)
    found = None

    while queue:
        state = queue.popleft()
        city, mask, day = state

        if city == 'V' and mask == all_visited:
            s_final = 29 - day
            if 1 <= s_final <= 5:
                found = (state, s_final)
                break

        max_stay = min(5, 29 - day - 1)
        if max_stay < 1:
            continue

        for s in range(1, max_stay + 1):
            leave_day = day + s
            for neighbor, travel_days, cost in graph[city]:
                arrival_day = leave_day + travel_days
                if arrival_day > 29:
                    continue
                neighbor_idx = city_to_index[neighbor]
                new_mask = mask | (1 << neighbor_idx)
                new_state = (neighbor, new_mask, arrival_day)
                
                if new_state in visited:
                    continue
                visited.add(new_state)
                parent[new_state] = (state, s)
                queue.append(new_state)

    if found is None:
        print("No solution found")
    else:
        final_state, s_final = found
        itinerary = []
        itinerary.append(('V', s_final))
        
        state = final_state
        while parent[state] != (None, None):
            prev_state, stay_duration = parent[state]
            prev_city = prev_state[0]
            itinerary.insert(0, (prev_city, stay_duration))
            state = prev_state
        
        print(itinerary)

if __name__ == '__main__':
    main()