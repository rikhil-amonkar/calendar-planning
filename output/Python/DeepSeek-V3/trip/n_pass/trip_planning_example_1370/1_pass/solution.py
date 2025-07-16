import json
from itertools import permutations

def main():
    # Cities and their required days
    city_days = {
        'Santorini': 5,
        'Krakow': 5,
        'Paris': 5,
        'Vilnius': 3,
        'Munich': 5,
        'Geneva': 2,
        'Amsterdam': 4,
        'Budapest': 5,
        'Split': 4
    }
    
    # Direct flights (undirected graph)
    direct_flights = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Vilnius', 'Munich'],
        'Krakow': ['Paris', 'Split', 'Munich', 'Amsterdam', 'Vilnius'],
        'Vilnius': ['Munich', 'Amsterdam', 'Paris', 'Split', 'Krakow'],
        'Munich': ['Vilnius', 'Split', 'Amsterdam', 'Geneva', 'Krakow', 'Paris', 'Budapest'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Budapest', 'Santorini'],
        'Amsterdam': ['Paris', 'Geneva', 'Munich', 'Budapest', 'Split', 'Vilnius', 'Krakow', 'Santorini'],
        'Budapest': ['Amsterdam', 'Paris', 'Geneva', 'Munich'],
        'Split': ['Paris', 'Munich', 'Amsterdam', 'Geneva', 'Vilnius', 'Krakow'],
        'Santorini': ['Geneva', 'Amsterdam']
    }
    
    # Constraints
    constraints = [
        ('Santorini', (25, 29)),
        ('Krakow', (18, 22)),
        ('Paris', (11, 15))
    ]
    
    # Generate all possible city orders (permutations)
    cities = list(city_days.keys())
    best_itinerary = None
    best_score = float('inf')
    
    # Since 9! is too large, we'll use a heuristic approach
    # We'll prioritize cities with tight constraints first
    constrained_cities = [city for city, _ in constraints]
    other_cities = [city for city in cities if city not in constrained_cities]
    
    # Try permutations of constrained cities first
    for perm in permutations(constrained_cities):
        # Try to place other cities in between
        current_order = []
        remaining_cities = other_cities.copy()
        
        # Insert constrained cities in order
        for city in perm:
            current_order.append(city)
            # Try to insert other cities between constrained ones
            if len(current_order) < len(perm):
                for other in remaining_cities:
                    last = current_order[-1]
                    if other in direct_flights[last]:
                        current_order.append(other)
                        remaining_cities.remove(other)
                        break
        
        # Add remaining cities at the end
        current_order.extend(remaining_cities)
        
        # Check if all flights are valid
        valid = True
        for i in range(len(current_order)-1):
            if current_order[i+1] not in direct_flights[current_order[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Try to assign days to this order
        itinerary = []
        current_day = 1
        remaining_days = city_days.copy()
        
        for city in current_order:
            days_needed = remaining_days[city]
            itinerary.append((current_day, current_day + days_needed - 1, city))
            current_day += days_needed
            remaining_days[city] = 0
        
        # Check if total days is 30
        if current_day - 1 != 30:
            continue
        
        # Check constraints
        constraints_met = True
        for city, (start, end) in constraints:
            found = False
            for (s, e, c) in itinerary:
                if c == city:
                    # Check if [s,e] overlaps with [start,end]
                    if not (e < start or s > end):
                        found = True
                        break
            if not found:
                constraints_met = False
                break
        if not constraints_met:
            continue
        
        # Calculate score (how well constraints are met)
        score = 0
        for city, (start, end) in constraints:
            for (s, e, c) in itinerary:
                if c == city:
                    # Penalize if not fully within window
                    if s < start or e > end:
                        score += 1
        if score < best_score:
            best_score = score
            best_itinerary = itinerary
    
    # If no perfect itinerary found, try relaxing constraints
    if best_itinerary is None:
        for perm in permutations(constrained_cities):
            current_order = []
            remaining_cities = other_cities.copy()
            
            for city in perm:
                current_order.append(city)
                if len(current_order) < len(perm):
                    for other in remaining_cities:
                        last = current_order[-1]
                        if other in direct_flights[last]:
                            current_order.append(other)
                            remaining_cities.remove(other)
                            break
            
            current_order.extend(remaining_cities)
            
            valid = True
            for i in range(len(current_order)-1):
                if current_order[i+1] not in direct_flights[current_order[i]]:
                    valid = False
                    break
            if not valid:
                continue
            
            itinerary = []
            current_day = 1
            remaining_days = city_days.copy()
            
            for city in current_order:
                days_needed = remaining_days[city]
                itinerary.append((current_day, current_day + days_needed - 1, city))
                current_day += days_needed
                remaining_days[city] = 0
            
            if current_day - 1 != 30:
                continue
            
            # Even if constraints aren't perfectly met, accept this
            best_itinerary = itinerary
            break
    
    # Format the output
    result = {"itinerary": []}
    for start, end, city in best_itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        result["itinerary"].append({"day_range": day_range, "place": city})
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()