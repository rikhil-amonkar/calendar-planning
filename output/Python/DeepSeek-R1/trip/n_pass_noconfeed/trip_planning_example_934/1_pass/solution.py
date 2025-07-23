import itertools
import json

def main():
    days_required = {
        'Brussels': 5,
        'Rome': 2,
        'Dubrovnik': 3,
        'Geneva': 5,
        'Budapest': 2,
        'Riga': 4,
        'Valencia': 2
    }
    
    window_constraints = {
        'Brussels': (7, 11),
        'Riga': (4, 7),
        'Budapest': (16, 17)
    }
    
    graph = {
        'Brussels': ['Valencia', 'Geneva', 'Riga', 'Rome', 'Budapest'],
        'Valencia': ['Brussels', 'Rome', 'Geneva'],
        'Rome': ['Valencia', 'Geneva', 'Riga', 'Budapest', 'Brussels', 'Dubrovnik'],
        'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
        'Dubrovnik': ['Geneva', 'Rome'],
        'Riga': ['Brussels'],
        'Budapest': ['Geneva', 'Rome', 'Brussels']
    }
    
    cities = list(days_required.keys())
    found = False
    result_itinerary = []
    
    for perm in itertools.permutations(cities):
        d = [days_required[city] for city in perm]
        a1 = d[0]
        a2 = a1 + d[1] - 1
        a3 = a2 + d[2] - 1
        a4 = a3 + d[3] - 1
        a5 = a4 + d[4] - 1
        a6 = a5 + d[5] - 1
        a_list = [a1, a2, a3, a4, a5, a6]
        
        last_segment_days = 17 - a6 + 1
        if last_segment_days != d[6]:
            continue
            
        valid_flight = True
        for i in range(6):
            from_city = perm[i]
            to_city = perm[i+1]
            if to_city not in graph.get(from_city, []):
                valid_flight = False
                break
                
        if not valid_flight:
            continue
            
        valid_time = True
        for city, (L, R) in window_constraints.items():
            j = perm.index(city)
            if j == 0:
                s, e = 1, a_list[0]
            elif j == 6:
                s, e = a_list[5], 17
            else:
                s, e = a_list[j-1], a_list[j]
                
            if not (s <= R and e >= L):
                valid_time = False
                break
                
        if valid_time:
            itinerary = []
            for idx, city in enumerate(perm):
                if idx == 0:
                    day_range_str = f"1-{a_list[0]}"
                elif idx == 6:
                    day_range_str = f"{a_list[5]}-17"
                else:
                    day_range_str = f"{a_list[idx-1]}-{a_list[idx]}"
                itinerary.append({"day_range": "Day " + day_range_str, "place": city})
            result_itinerary = itinerary
            found = True
            break
            
    result = {"itinerary": result_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()