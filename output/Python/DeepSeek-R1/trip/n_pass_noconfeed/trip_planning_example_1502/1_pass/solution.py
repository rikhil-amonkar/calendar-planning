import json
from collections import defaultdict

def main():
    cities = ['Bucharest', 'Frankfurt', 'Krakow', 'Madrid', 'Riga', 'Santorini', 'Seville', 'Tallinn', 'Valencia', 'Vienna']
    req = [3, 4, 5, 2, 4, 3, 2, 5, 4, 4]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    index_to_city = {idx: city for idx, city in enumerate(cities)}
    
    direct_flights = [
        ('Vienna', 'Bucharest'),
        ('Santorini', 'Madrid'),
        ('Seville', 'Valencia'),
        ('Vienna', 'Seville'),
        ('Madrid', 'Valencia'),
        ('Bucharest', 'Riga'),
        ('Valencia', 'Bucharest'),
        ('Santorini', 'Bucharest'),
        ('Vienna', 'Valencia'),
        ('Vienna', 'Madrid'),
        ('Valencia', 'Krakow'),
        ('Valencia', 'Frankfurt'),
        ('Krakow', 'Frankfurt'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Krakow'),
        ('Vienna', 'Frankfurt'),
        ('Madrid', 'Seville'),
        ('Santorini', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Frankfurt', 'Tallinn'),
        ('Frankfurt', 'Bucharest'),
        ('Madrid', 'Bucharest'),
        ('Frankfurt', 'Riga'),
        ('Madrid', 'Frankfurt')
    ]
    
    graph = defaultdict(set)
    for a, b in direct_flights:
        graph[a].add(b)
        graph[b].add(a)
    for city in cities:
        graph[city].add(city)
    
    fixed_events = {
        3: ['Vienna'],
        4: ['Vienna'],
        5: ['Vienna'],
        6: ['Vienna', 'Madrid'],
        7: ['Madrid'],
        11: ['Krakow'],
        12: ['Krakow'],
        13: ['Krakow'],
        14: ['Krakow'],
        15: ['Krakow'],
        20: ['Riga'],
        21: ['Riga'],
        22: ['Riga'],
        23: ['Riga', 'Tallinn'],
        24: ['Tallinn'],
        25: ['Tallinn'],
        26: ['Tallinn'],
        27: ['Tallinn']
    }
    
    memo = {}
    req_tuple = tuple(req)
    
    def dfs(current_city, day, spent_tuple):
        if day > 27:
            if spent_tuple == req_tuple:
                return (True, [])
            else:
                return (False, None)
        
        key = (current_city, day, spent_tuple)
        if key in memo:
            return memo[key]
        
        if day in fixed_events:
            for cityX in fixed_events[day]:
                if current_city != cityX and cityX not in graph[current_city]:
                    memo[key] = (False, None)
                    return (False, None)
        
        spent_list = list(spent_tuple)
        idx_current = city_to_index[current_city]
        
        new_spent1 = spent_list[:]
        new_spent1[idx_current] += 1
        if new_spent1[idx_current] <= req_tuple[idx_current]:
            if day == 27:
                if tuple(new_spent1) == req_tuple:
                    memo[key] = (True, [current_city])
                    return (True, [current_city])
            else:
                success, path = dfs(current_city, day+1, tuple(new_spent1))
                if success:
                    full_path = [current_city] + path
                    memo[key] = (True, full_path)
                    return (True, full_path)
        
        for next_city in graph[current_city]:
            if next_city == current_city:
                continue
            new_spent2 = spent_list[:]
            idx_next = city_to_index[next_city]
            new_spent2[idx_current] += 1
            new_spent2[idx_next] += 1
            if new_spent2[idx_current] <= req_tuple[idx_current] and new_spent2[idx_next] <= req_tuple[idx_next]:
                if day == 27:
                    if tuple(new_spent2) == req_tuple:
                        memo[key] = (True, [next_city])
                        return (True, [next_city])
                else:
                    success, path = dfs(next_city, day+1, tuple(new_spent2))
                    if success:
                        full_path = [next_city] + path
                        memo[key] = (True, full_path)
                        return (True, full_path)
        
        memo[key] = (False, None)
        return (False, None)
    
    for start_city in cities:
        initial_spent = [0] * len(cities)
        idx_start = city_to_index[start_city]
        initial_spent[idx_start] = 1
        success, path = dfs(start_city, 2, tuple(initial_spent))
        if success:
            break
    else:
        print('{"itinerary": []}')
        return
    
    itinerary_sequence = [start_city] + path if not path or path[0] != start_city else path
    
    itinerary_ranges = []
    start_day = 1
    current_city = itinerary_sequence[0]
    for day in range(2, 28):
        if itinerary_sequence[day-1] != current_city:
            end_day = day - 1
            itinerary_ranges.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": current_city
            })
            start_day = day
            current_city = itinerary_sequence[day-1]
    itinerary_ranges.append({
        "day_range": f"Day {start_day}-27",
        "place": current_city
    })
    
    result = {"itinerary": itinerary_ranges}
    print(json.dumps(result))

if __name__ == "__main__":
    main()