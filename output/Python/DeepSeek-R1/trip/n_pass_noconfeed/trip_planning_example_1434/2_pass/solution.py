import itertools
import json

def main():
    days_dict = {
        'Rome': 3,
        'Mykonos': 2,
        'Lisbon': 2,
        'Frankfurt': 5,
        'Nice': 3,
        'Stuttgart': 4,
        'Venice': 4,
        'Dublin': 2,
        'Bucharest': 2,
        'Seville': 5
    }
    
    flights = [
        "Rome and Stuttgart", 
        "Venice and Rome", 
        "Dublin and Bucharest", 
        "Mykonos and Rome", 
        "Seville and Lisbon", 
        "Frankfurt and Venice", 
        "Venice and Stuttgart", 
        "Bucharest and Lisbon", 
        "Nice and Mykonos", 
        "Venice and Lisbon", 
        "Dublin and Lisbon", 
        "Venice and Nice", 
        "Rome and Seville", 
        "Frankfurt and Rome", 
        "Nice and Dublin", 
        "Rome and Bucharest", 
        "Frankfurt and Dublin", 
        "Rome and Dublin", 
        "Venice and Dublin", 
        "Rome and Lisbon", 
        "Frankfurt and Lisbon", 
        "Nice and Rome", 
        "Frankfurt and Nice", 
        "Frankfurt and Stuttgart", 
        "Frankfurt and Bucharest", 
        "Lisbon and Stuttgart", 
        "Nice and Lisbon", 
        "Seville and Dublin"
    ]
    
    graph = set()
    for flight in flights:
        parts = flight.split(' and ')
        city1, city2 = parts[0], parts[1]
        edge = tuple(sorted([city1, city2]))
        graph.add(edge)
    
    def are_connected(c1, c2):
        return tuple(sorted([c1, c2])) in graph
        
    fixed_cities = ['Frankfurt', 'Mykonos', 'Seville']
    remaining_cities = ['Rome', 'Lisbon', 'Nice', 'Stuttgart', 'Venice', 'Dublin', 'Bucharest']
    n_remaining = len(remaining_cities)
    solution_found = False
    itinerary_result = []
    
    for bitmask in range(1, 1 << n_remaining):
        subset = []
        total_days = 0
        for i in range(n_remaining):
            if bitmask & (1 << i):
                city = remaining_cities[i]
                subset.append(city)
                total_days += days_dict[city]
                
        if total_days != 11:
            continue
            
        full_cities = fixed_cities + subset
        n = len(full_cities)
        
        for perm in itertools.permutations(full_cities):
            valid_path = True
            for j in range(n-1):
                if not are_connected(perm[j], perm[j+1]):
                    valid_path = False
                    break
            if not valid_path:
                continue
                
            starts = [1]
            for j in range(n-1):
                next_start = starts[j] + days_dict[perm[j]]
                starts.append(next_start)
                
            last_end = starts[-1] + days_dict[perm[-1]] - 1
            if last_end != 23:
                continue
                
            mykonos_start = None
            frankfurt_start = None
            seville_start = None
            for idx, city in enumerate(perm):
                if city == 'Mykonos':
                    mykonos_start = starts[idx]
                elif city == 'Frankfurt':
                    frankfurt_start = starts[idx]
                elif city == 'Seville':
                    seville_start = starts[idx]
                    
            if mykonos_start is None or frankfurt_start is None or seville_start is None:
                continue
                
            if mykonos_start <= 11 and frankfurt_start <= 5 and seville_start == 13:
                itinerary_list = []
                for idx, city in enumerate(perm):
                    start_day = starts[idx]
                    end_day = start_day + days_dict[city] - 1
                    day_range = f"Day {start_day}-{end_day}"
                    itinerary_list.append({"day_range": day_range, "place": city})
                itinerary_result = itinerary_list
                solution_found = True
                break
        if solution_found:
            break
            
    if solution_found:
        print(json.dumps({"itinerary": itinerary_result}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()