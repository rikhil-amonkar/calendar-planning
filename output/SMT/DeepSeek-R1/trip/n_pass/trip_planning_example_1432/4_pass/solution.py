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
    min_days = [[10**9] * (1 << n) for _ in range(n)]
    parent = {}
    queue = deque()
    start_city = 'V'
    start_mask = 1 << city_to_index[start_city]
    start_day = 0
    start_state = (start_city, start_mask, start_day)
    min_days[city_to_index[start_city]][start_mask] = 0
    queue.append(start_state)
    parent[start_state] = (None, None)
    found = None

    while queue:
        city, mask, day = queue.popleft()
        cidx = city_to_index[city]
        
        if city == 'V' and mask == all_visited:
            s_final = 29 - day
            if 1 <= s_final <= 5:
                found = ( (city, mask, day), s_final )
                break
                
        for s in range(1, 6):
            if day + s >= 28:
                break
            leave_day = day + s
            for neighbor, travel_days, cost in graph[city]:
                arrival_day = leave_day + travel_days
                if arrival_day > 28:
                    continue
                nidx = city_to_index[neighbor]
                new_mask = mask | (1 << nidx)
                if arrival_day < min_days[nidx][new_mask]:
                    min_days[nidx][new_mask] = arrival_day
                    new_state = (neighbor, new_mask, arrival_day)
                    parent[new_state] = ((city, mask, day), s)
                    queue.append(new_state)
                    
    if found is None:
        print("No solution found")
    else:
        final_state, s_final = found
        itinerary = []
        itinerary.append(('V', s_final))
        
        state = final_state
        while parent[state] != (None, None):
            state, stay_duration = parent[state]
            if parent[state] == (None, None):
                break
            prev_state, prev_stay = parent[state]
            itinerary.append((state[0], stay_duration))
            state = prev_state
        
        itinerary.append(('V', state[2]))
        itinerary.reverse()
        print(itinerary)

if __name__ == '__main__':
    main()