import json
from itertools import permutations

def main():
    total_days = 12
    city_days = {
        "Vilnius": 4,
        "Munich": 3,
        "Mykonos": 7
    }
    
    graph = {
        "Vilnius": ["Munich"],
        "Munich": ["Mykonos"],
        "Mykonos": ["Munich"]
    }
    
    cities = list(city_days.keys())
    perms = permutations(cities)
    found_order = None
    
    for perm in perms:
        valid = True
        for i in range(len(perm) - 1):
            from_city = perm[i]
            to_city = perm[i+1]
            if to_city not in graph.get(from_city, []):
                valid = False
                break
        if valid:
            found_order = perm
            break
            
    if found_order is None:
        result = {"itinerary": []}
        print(json.dumps(result))
        return
        
    current_start = 1
    itinerary_list = []
    for city in found_order:
        num_days = city_days[city]
        end_day = current_start + num_days - 1
        itinerary_list.append({
            "day_range": f"Day {current_start}-{end_day}",
            "place": city
        })
        current_start = end_day
        
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()