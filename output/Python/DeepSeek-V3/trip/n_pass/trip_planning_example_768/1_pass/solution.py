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
    
    # Conference constraints
    conference_days = [14, 15, 16]  # Days 14-16 in Nice
    
    # Friend meeting constraint in Oslo between day 10 and 14
    oslo_friend_days = list(range(10, 15))  # Days 10-14
    
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
            
            # Check if Nice is assigned during conference days
            if city == "Nice":
                nice_days = []
                # Must include days 14-16 in Nice
                if current_day > 14:
                    valid_order = False
                    break
                end_day = min(current_day + required_days - 1, 16)
                nice_days = list(range(current_day, end_day + 1))
                if not all(day in nice_days for day in conference_days):
                    valid_order = False
                    break
                days_assigned["Nice"] = len(nice_days)
                itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Nice"})
                current_day = end_day + 1
                continue
            
            # Check if Oslo is assigned during friend days
            if city == "Oslo":
                oslo_days = []
                end_day = current_day + required_days - 1
                oslo_days = list(range(current_day, end_day + 1))
                # At least one day must overlap with friend days
                if not any(day in oslo_friend_days for day in oslo_days):
                    valid_order = False
                    break
                days_assigned["Oslo"] = len(oslo_days)
                itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Oslo"})
                current_day = end_day + 1
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
print(json.dumps(result))