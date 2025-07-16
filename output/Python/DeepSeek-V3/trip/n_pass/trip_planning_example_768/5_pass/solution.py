import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4
    }
    
    # Direct flights
    direct_flights = {
        "London": ["Copenhagen", "Mykonos", "Nice", "Oslo"],
        "Copenhagen": ["London", "Tallinn", "Nice", "Oslo"],
        "Tallinn": ["Copenhagen", "Oslo"],
        "Mykonos": ["London", "Nice"],
        "Oslo": ["Tallinn", "Nice", "London", "Copenhagen"],
        "Nice": ["Oslo", "London", "Mykonos", "Copenhagen"]
    }
    
    total_days = 16
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    for order in possible_orders:
        # Nice must be last
        if order[-1] != "Nice":
            continue
            
        # Check flight connections between consecutive cities
        valid_flights = True
        for i in range(len(order)-1):
            current = order[i]
            next_city = order[i+1]
            if next_city not in direct_flights[current]:
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Try to assign days to cities
        itinerary = []
        used_days = [False] * (total_days + 2)  # 1-based indexing
        
        # Assign Nice first (days 14-16)
        nice_start = 14
        nice_end = 16
        for day in range(nice_start, nice_end + 1):
            used_days[day] = True
        itinerary.append({
            "day_range": f"Day {nice_start}-{nice_end}",
            "place": "Nice"
        })
        
        remaining_cities = order[:-1]  # all cities except Nice
        remaining_days = total_days - cities["Nice"]
        
        # Try all possible positions for Oslo to satisfy its constraint
        if "Oslo" in remaining_cities:
            oslo_days = cities["Oslo"]
            # Oslo must include at least one day between 10-14
            possible_oslo_starts = []
            for start in range(1, total_days - oslo_days + 2):
                end = start + oslo_days - 1
                if any(day in range(10, 15) for day in range(start, end + 1)) and end < nice_start:
                    possible_oslo_starts.append(start)
            
            for oslo_start in possible_oslo_starts:
                # Create a copy to backtrack if needed
                temp_used = used_days.copy()
                temp_itinerary = itinerary.copy()
                
                oslo_end = oslo_start + oslo_days - 1
                for day in range(oslo_start, oslo_end + 1):
                    if temp_used[day]:
                        break  # conflict, try next position
                else:
                    # Assign Oslo
                    for day in range(oslo_start, oslo_end + 1):
                        temp_used[day] = True
                    temp_itinerary.append({
                        "day_range": f"Day {oslo_start}-{oslo_end}",
                        "place": "Oslo"
                    })
                    
                    # Assign remaining cities
                    success = True
                    for city in remaining_cities:
                        if city == "Oslo":
                            continue
                            
                        city_days = cities[city]
                        assigned = False
                        
                        # Find earliest available consecutive days
                        for start in range(1, total_days - city_days + 2):
                            end = start + city_days - 1
                            if end >= nice_start:
                                continue
                            
                            # Check if all days are available
                            available = True
                            for day in range(start, end + 1):
                                if temp_used[day]:
                                    available = False
                                    break
                            
                            if available:
                                for day in range(start, end + 1):
                                    temp_used[day] = True
                                temp_itinerary.append({
                                    "day_range": f"Day {start}-{end}",
                                    "place": city
                                })
                                assigned = True
                                break
                        
                        if not assigned:
                            success = False
                            break
                    
                    if success:
                        # Sort by day range and return
                        temp_itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
                        return {"itinerary": temp_itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))