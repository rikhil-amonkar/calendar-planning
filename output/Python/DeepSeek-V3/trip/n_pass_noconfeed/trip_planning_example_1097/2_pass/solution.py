import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3
    }
    
    # Direct flights (undirected graph)
    flights = {
        "Warsaw": ["Reykjavik", "Riga", "London", "Oslo", "Madrid"],
        "Reykjavik": ["Warsaw", "Madrid", "Oslo", "London"],
        "Oslo": ["Madrid", "Warsaw", "Dubrovnik", "Riga", "Lyon", "London", "Reykjavik"],
        "Riga": ["Warsaw", "Oslo"],
        "Lyon": ["London", "Oslo", "Madrid"],
        "Dubrovnik": ["Oslo", "Madrid"],
        "Madrid": ["Oslo", "London", "Warsaw", "Lyon", "Dubrovnik", "Reykjavik"],
        "London": ["Lyon", "Madrid", "Warsaw", "Oslo", "Reykjavik"]
    }
    
    # Constraints
    constraints = [
        ("Riga", (4, 5)),  # Meet friend in Riga between day 4 and 5
        ("Dubrovnik", (7, 8))  # Wedding in Dubrovnik between day 7 and 8
    ]
    
    # Fix typos in city names
    cities["Warsaw"] = cities.pop("Warsaw")
    cities["Madrid"] = cities.pop("Madrid")
    cities["Dubrovnik"] = cities.pop("Dubrovnik")
    
    # Generate all possible permutations of cities, but prioritize constrained cities
    constrained_cities = [city for city, _ in constraints]
    other_cities = [city for city in cities if city not in constrained_cities]
    
    # Try different orders of constrained cities
    for constrained_order in permutations(constrained_cities):
        # Try different orders of other cities
        for other_order in permutations(other_cities):
            # Combine the orders
            perm = list(constrained_order) + list(other_order)
            
            itinerary = []
            current_day = 1
            valid = True
            prev_city = None
            remaining_days = cities.copy()
            
            for city in perm:
                if prev_city is not None:
                    # Check if flight exists
                    if city not in flights.get(prev_city, []):
                        valid = False
                        break
                    # Transition day (counts for both cities)
                    remaining_days[prev_city] -= 1
                    remaining_days[city] -= 1
                    if remaining_days[prev_city] < 0 or remaining_days[city] < 0:
                        valid = False
                        break
                    current_day += 1
                
                # Stay in the city for remaining days
                stay_days = remaining_days[city]
                if stay_days <= 0:
                    valid = False
                    break
                itinerary.append((current_day, current_day + stay_days - 1, city))
                current_day += stay_days
                remaining_days[city] = 0
                prev_city = city
            
            # Check if all days are used
            if current_day - 1 != 18:
                valid = False
            
            # Check constraints
            if valid:
                for constraint_city, (start_day, end_day) in constraints:
                    found = False
                    for (start, end, city) in itinerary:
                        if city == constraint_city:
                            if start <= end_day and end >= start_day:
                                found = True
                                break
                    if not found:
                        valid = False
                        break
            
            if valid:
                # Format itinerary
                formatted_itinerary = []
                for start, end, city in itinerary:
                    if start == end:
                        day_range = f"Day {start}"
                    else:
                        day_range = f"Day {start}-{end}"
                    formatted_itinerary.append({"day_range": day_range, "place": city})
                return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Execute and print result
result = find_itinerary()
print(json.dumps(result, indent=2))