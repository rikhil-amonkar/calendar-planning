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
        
        for city in order:
            required_days = cities[city]
            
            # Nice must include days 14-16
            if city == "Nice":
                # Nice must start on day 14 - 3 + 1 = day 12 to include days 14-16
                nice_start = max(12, current_day)
                end_day = nice_start + required_days - 1
                if end_day > total_days:
                    valid_order = False
                    break
                if not (nice_start <= 14 and end_day >= 16):
                    valid_order = False
                    break
                days_assigned["Nice"] = required_days
                itinerary.append({"day_range": f"Day {nice_start}-{end_day}", "place": "Nice"})
                current_day = end_day + 1
                continue
            
            # Oslo must include at least one day between 10-14
            if city == "Oslo":
                # Find earliest possible start that includes at least one day in 10-14
                earliest_start = max(1, 10 - required_days + 1)
                latest_start = 14
                
                # Find possible start days for Oslo
                possible_starts = range(max(current_day, earliest_start), latest_start + 1)
                found = False
                
                for start in possible_starts:
                    end = start + required_days - 1
                    if end > total_days:
                        continue
                    if any(day in range(10, 15) for day in range(start, end + 1)):
                        days_assigned["Oslo"] = required_days
                        itinerary.append({"day_range": f"Day {start}-{end}", "place": "Oslo"})
                        current_day = end + 1
                        found = True
                        break
                
                if not found:
                    valid_order = False
                continue
            
            # Assign days for other cities
            end_day = current_day + required_days - 1
            if end_day > total_days:
                valid_order = False
                break
            days_assigned[city] = required_days
            itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
            current_day = end_day + 1
        
        # Check if all days are assigned correctly
        if valid_order and current_day > total_days and all(days_assigned[city] == cities[city] for city in cities):
            valid_itineraries.append(itinerary)
    
    if valid_itineraries:
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))