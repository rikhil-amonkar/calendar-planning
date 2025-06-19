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
    total_days_target = 29
    memo = set()
    
    def dfs(current_city, current_day, visited, path, stays):
        if current_city == 'V' and visited == all_visited:
            s_last = total_days_target - current_day
            if 1 <= s_last <= 5:
                return path, stays + [s_last]
            else:
                return None
        
        for s in range(1, 6):
            departure_day = current_day + s
            if departure_day >= total_days_target:
                continue
                
            neighbors = graph[current_city]
            neighbors_sorted = sorted(neighbors, key=lambda x: x[1])
            for neighbor, travel_days, cost in neighbors_sorted:
                arrival_day = departure_day + travel_days
                if arrival_day > total_days_target:
                    continue
                    
                neighbor_idx = city_to_index[neighbor]
                new_visited = visited | (1 << neighbor_idx)
                
                state_key = (neighbor, arrival_day, new_visited)
                if state_key in memo:
                    continue
                memo.add(state_key)
                
                new_path = path + [neighbor]
                new_stays = stays + [s]
                result = dfs(neighbor, arrival_day, new_visited, new_path, new_stays)
                if result is not None:
                    return result
                    
        return None
        
    start_city = 'V'
    start_day = 0
    start_visited = 1 << city_to_index['V']
    start_path = ['V']
    start_stays = []
    
    result = dfs(start_city, start_day, start_visited, start_path, start_stays)
    if result is None:
        print("No solution found")
    else:
        path, stays = result
        itinerary = list(zip(path, stays))
        print(itinerary)

if __name__ == '__main__':
    main()