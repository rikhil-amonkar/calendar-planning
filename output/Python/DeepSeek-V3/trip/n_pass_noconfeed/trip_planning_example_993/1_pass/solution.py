import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }
    
    # Direct flights
    direct_flights = {
        "London": ["Amsterdam", "Bucharest", "Frankfurt", "Stockholm"],
        "Amsterdam": ["London", "Stockholm", "Frankfurt", "Riga", "Bucharest", "Vilnius"],
        "Vilnius": ["Frankfurt", "Riga", "Amsterdam"],
        "Riga": ["Vilnius", "Stockholm", "Frankfurt", "Bucharest", "Amsterdam"],
        "Frankfurt": ["Vilnius", "Amsterdam", "Stockholm", "Riga", "Bucharest", "London"],
        "Stockholm": ["Riga", "Amsterdam", "Frankfurt", "London"],
        "Bucharest": ["London", "Amsterdam", "Riga", "Frankfurt"]
    }
    
    # Constraints
    constraints = [
        ("Amsterdam", 2, 3),  # Meet friend between day 2 and 3
        ("Vilnius", 7, 11),   # Workshop between day 7 and 11
        ("Stockholm", 13, 15) # Wedding between day 13 and 15
    ]
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    for order in possible_orders:
        # Check if all cities are connected by direct flights
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in direct_flights[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Try to assign days to this order
        itinerary = []
        current_day = 1
        remaining_cities = list(order)
        remaining_days = cities.copy()
        
        # Assign days to each city in order
        temp_itinerary = []
        for city in order:
            days_needed = remaining_days[city]
            end_day = current_day + days_needed - 1
            temp_itinerary.append({
                "city": city,
                "start_day": current_day,
                "end_day": end_day
            })
            current_day = end_day + 1
        
        # Check constraints
        meets_constraints = True
        for constraint_city, start, end in constraints:
            found = False
            for entry in temp_itinerary:
                if entry["city"] == constraint_city:
                    # Check if the constraint days overlap with the visit
                    if not (entry["end_day"] < start or entry["start_day"] > end):
                        found = True
                        break
            if not found:
                meets_constraints = False
                break
        
        if meets_constraints:
            # Check if all days are covered (15 days)
            total_days = sum(cities.values())
            if total_days == 15:
                # Format the itinerary
                formatted_itinerary = []
                for entry in temp_itinerary:
                    if entry["start_day"] == entry["end_day"]:
                        day_range = f"Day {entry['start_day']}"
                    else:
                        day_range = f"Day {entry['start_day']}-{entry['end_day']}"
                    formatted_itinerary.append({
                        "day_range": day_range,
                        "place": entry["city"]
                    })
                return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))