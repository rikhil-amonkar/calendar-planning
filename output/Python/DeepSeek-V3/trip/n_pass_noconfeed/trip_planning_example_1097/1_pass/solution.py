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
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if all cities are included
        if set(perm) != set(cities.keys()):
            continue
        
        # Try to build itinerary
        prev_city = None
        remaining_days = cities.copy()
        
        for city in perm:
            if prev_city is None:
                # First city
                prev_city = city
            else:
                # Check if flight exists
                if city not in flights[prev_city]:
                    valid = False
                    break
                # Transition day (counts for both cities)
                remaining_days[prev_city] -= 1
                remaining_days[city] -= 1
                if remaining_days[prev_city] < 0 or remaining_days[city] < 0:
                    valid = False
                    break
                current_day += 1
                prev_city = city
            
            # Stay in the city for remaining days
            stay_days = remaining_days[city]
            if stay_days <= 0:
                valid = False
                break
            itinerary.append((current_day, current_day + stay_days - 1, city))
            current_day += stay_days
            remaining_days[city] = 0
        
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