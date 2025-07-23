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
    istanbul_relatives = (6, 7)
    santorini_wedding = (13, 16)
    
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
        itinerary = []
        remaining_days = 16
        current_day = 1
        
        # Assign Santorini first because of the wedding constraint
        # We know Santorini must be last because wedding is days 13-16
        if perm[-1] != 'Santorini':
            continue
        
        # Assign Istanbul next because of relatives constraint
        # Istanbul must include day 6 or 7
        # Try to place Istanbul in a position where it covers day 6 or 7
        # This is complex, so we'll proceed with a simplified approach
        
        # Assign days to each city in order
        day_assignments = []
        for city in perm:
            req_days = cities[city]
            day_assignments.append((current_day, current_day + req_days - 1, city))
            current_day += req_days
        
        # Check if assignments meet constraints
        meets_constraints = True
        
        # Check Istanbul relatives constraint
        istanbul_found = False
        for start, end, city in day_assignments:
            if city == 'Istanbul':
                istanbul_found = True
                if not (start <= istanbul_relatives[0] <= end or start <= istanbul_relatives[1] <= end):
                    meets_constraints = False
                    break
        if not istanbul_found:
            meets_constraints = False
        
        # Check Santorini wedding constraint
        santorini_found = False
        for start, end, city in day_assignments:
            if city == 'Santorini':
                santorini_found = True
                if not (start <= santorini_wedding[0] and end >= santorini_wedding[1]):
                    meets_constraints = False
                    break
        if not santorini_found:
            meets_constraints = False
        
        # Check total days
        total_days = sum(cities.values())
        if total_days != 16:
            meets_constraints = False
        
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
    
    # If no valid itinerary found (shouldn't happen with given constraints)
    return {"itinerary": []}

# Find and print the itinerary
result = find_itinerary()
print(json.dumps(result))