import json
from itertools import permutations

def find_itinerary():
    # Cities and required days (excluding transition day)
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
    
    # Try different starting cities
    for start_city in cities:
        # Try different orders of remaining cities
        remaining_cities = [city for city in cities if city != start_city]
        
        for perm in permutations(remaining_cities):
            itinerary = []
            current_day = 1
            valid = True
            prev_city = start_city
            
            # Add starting city
            stay_days = cities[start_city]
            itinerary.append((current_day, current_day + stay_days - 1, start_city))
            current_day += stay_days
            
            for city in perm:
                # Check if flight exists
                if city not in flights.get(prev_city, []):
                    valid = False
                    break
                
                # Add transition day (counts as a day but no city)
                current_day += 1
                
                # Stay in the city for required days
                stay_days = cities[city]
                itinerary.append((current_day, current_day + stay_days - 1, city))
                current_day += stay_days
                prev_city = city
            
            # Check total days (18 days including transition days)
            if current_day - 1 != 18:
                valid = False
            
            # Check constraints
            if valid:
                for constraint_city, (start_day, end_day) in constraints:
                    found = False
                    for (start, end, city) in itinerary:
                        if city == constraint_city:
                            # Check if any day in the stay overlaps with constraint window
                            if not (end < start_day or start > end_day):
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