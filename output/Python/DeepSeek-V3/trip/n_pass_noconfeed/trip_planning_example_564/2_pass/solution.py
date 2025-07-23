import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        'Istanbul': 2,
        'Rome': 3,
        'Seville': 4,
        'Naples': 7,
        'Santorini': 4
    }
    
    # Direct flights
    flights = {
        'Rome': ['Santorini', 'Seville', 'Naples', 'Istanbul'],
        'Santorini': ['Rome', 'Naples'],
        'Seville': ['Rome'],
        'Naples': ['Istanbul', 'Santorini', 'Rome'],
        'Istanbul': ['Naples', 'Rome']
    }
    
    # Constraints
    istanbul_relatives = (6, 7)  # Must include day 6 or 7
    santorini_wedding = (13, 16)  # Must be during days 13-16 (inclusive)
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        # Check if the permutation is feasible based on flight connections
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flights[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Try to assign days to this permutation
        current_day = 1
        day_assignments = []
        
        for city in perm:
            req_days = cities[city]
            day_assignments.append((current_day, current_day + req_days - 1, city))
            current_day += req_days
        
        # Check if total days exceed 16
        if day_assignments[-1][1] > 16:
            continue
        
        # Check constraints
        meets_constraints = True
        
        # Istanbul must include day 6 or 7
        istanbul_ok = False
        for start, end, city in day_assignments:
            if city == 'Istanbul':
                if (start <= 6 <= end) or (start <= 7 <= end):
                    istanbul_ok = True
                    break
        if not istanbul_ok:
            meets_constraints = False
            continue
        
        # Santorini must be days 13-16 (must start before day 13 and end after day 16)
        santorini_ok = False
        for start, end, city in day_assignments:
            if city == 'Santorini':
                if start <= 13 and end >= 16:
                    santorini_ok = True
                    break
        if not santorini_ok:
            meets_constraints = False
            continue
        
        if meets_constraints:
            # Format the itinerary
            formatted_itinerary = []
            for start, end, city in day_assignments:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                formatted_itinerary.append({"day_range": day_range, "place": city})
            
            return {"itinerary": formatted_itinerary}
    
    # If no valid itinerary found
    return {"itinerary": []}

# Find and print the itinerary
result = find_itinerary()
print(json.dumps(result, indent=2))