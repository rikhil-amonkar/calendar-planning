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
    
    # Total days
    total_days = 16
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if all transitions have direct flights
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in direct_flights[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Try to assign days to this order
        days_assigned = {city: 0 for city in city_names}
        itinerary = []
        current_day = 1
        
        # First assign Nice (must be last 3 days)
        if "Nice" not in order[-1:]:
            continue  # Nice must be last city
        
        # Assign Nice first (fixed position)
        nice_days = cities["Nice"]
        nice_start = total_days - nice_days + 1
        if nice_start != 14:  # Days 14-16
            continue
        days_assigned["Nice"] = nice_days
        itinerary.append({"day_range": "Day 14-16", "place": "Nice"})
        
        # Now assign other cities
        remaining_cities = [city for city in order if city != "Nice"]
        current_day = 1
        
        for city in remaining_cities:
            required_days = cities[city]
            
            # Oslo must include at least one day between 10-14
            if city == "Oslo":
                # Possible Oslo windows that include at least one day 10-14
                possible_starts = list(range(max(current_day, 6), 11))  # Latest start is day 10 (10+5-1=14)
                found = False
                for start in possible_starts:
                    end = start + required_days - 1
                    if end >= nice_start:
                        continue  # Overlaps with Nice
                    if any(day in range(10, 15) for day in range(start, end + 1)):
                        days_assigned[city] = required_days
                        itinerary.insert(0, {"day_range": f"Day {start}-{end}", "place": city})
                        current_day = end + 1
                        found = True
                        break
                if not found:
                    valid_order = False
                    break
                continue
            
            # Assign days for other cities
            end_day = current_day + required_days - 1
            if end_day >= nice_start:
                valid_order = False
                break
            days_assigned[city] = required_days
            itinerary.insert(0, {"day_range": f"Day {current_day}-{end_day}", "place": city})
            current_day = end_day + 1
        
        # Check if all days are assigned correctly
        if valid_order and current_day <= nice_start and all(days_assigned[city] == cities[city] for city in cities):
            # Sort itinerary by day range
            itinerary_sorted = sorted(itinerary, key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
            valid_itineraries.append(itinerary_sorted)
    
    if valid_itineraries:
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))