import json
from itertools import permutations

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Reykjavik': 4,
        'Riga': 2,
        'Oslo': 3,
        'Lyon': 5,
        'Dubrovnik': 2,
        'Madrid': 2,
        'Warsaw': 4,
        'London': 3
    }
    
    # Define flight connections (undirected)
    connections = {
        'Warsaw': ['Reykjavik', 'Riga', 'London', 'Oslo', 'Madrid'],
        'Reykjavik': ['Warsaw', 'Madrid', 'Oslo', 'London'],
        'Oslo': ['Madrid', 'Warsaw', 'Dubrovnik', 'Riga', 'Lyon', 'London', 'Reykjavik'],
        'Riga': ['Warsaw', 'Oslo'],
        'Lyon': ['London', 'Madrid', 'Oslo'],
        'Madrid': ['Oslo', 'London', 'Lyon', 'Dubrovnik', 'Warsaw', 'Reykjavik'],
        'Dubrovnik': ['Oslo', 'Madrid'],
        'London': ['Lyon', 'Madrid', 'Warsaw', 'Oslo', 'Reykjavik']
    }
    
    # Special constraints
    wedding_day = (7, 8)  # Must be in Dubrovnik between day 7-8
    riga_meet = (4, 5)    # Must be in Riga between day 4-5
    
    # Generate all possible permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if the permutation is valid (connected path)
        for i in range(len(perm) - 1):
            if perm[i+1] not in connections[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Assign days to each city in the permutation
        temp_itinerary = []
        remaining_days = cities.copy()
        for city in perm:
            days_needed = remaining_days[city]
            temp_itinerary.append((city, days_needed))
            del remaining_days[city]
        
        # Check if total days match
        total_days = sum(days for city, days in temp_itinerary)
        if total_days != 18:
            continue
        
        # Build day-by-day itinerary
        day_place = {}
        current_day = 1
        for city, days in temp_itinerary:
            end_day = current_day + days - 1
            day_place[(current_day, end_day)] = city
            current_day = end_day + 1
        
        # Check wedding constraint
        wedding_ok = False
        for (start, end), city in day_place.items():
            if city == 'Dubrovnik' and start <= wedding_day[0] and end >= wedding_day[1]:
                wedding_ok = True
                break
        if not wedding_ok:
            continue
        
        # Check Riga meet constraint
        riga_ok = False
        for (start, end), city in day_place.items():
            if city == 'Riga' and start <= riga_meet[0] and end >= riga_meet[1]:
                riga_ok = True
                break
        if not riga_ok:
            continue
        
        # If all constraints satisfied, format the itinerary
        formatted_itinerary = []
        for (start, end), city in sorted(day_place.items()):
            if start == end:
                day_str = f"Day {start}"
            else:
                day_str = f"Day {start}-{end}"
            formatted_itinerary.append({"day_range": day_str, "place": city})
        
        return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}  # Fallback if no solution found

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))