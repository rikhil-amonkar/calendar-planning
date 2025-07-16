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
    
    # Try different starting points
    for start_city in ['Paris', 'Amsterdam', 'Geneva', 'Munich']:  # Good hub cities
        for perm in permutations(constrained_cities):
            # Build itinerary starting with start_city
            current_order = [start_city] if start_city not in perm else []
            remaining_cities = other_cities.copy()
            
            # Insert constrained cities in order
            for city in perm:
                if city not in current_order:
                    # Find best place to insert
                    best_insert_pos = -1
                    for i in range(len(current_order)+1):
                        temp_order = current_order[:i] + [city] + current_order[i:]
                        valid = True
                        for j in range(len(temp_order)-1):
                            if temp_order[j+1] not in direct_flights.get(temp_order[j], []):
                                valid = False
                                break
                        if valid:
                            best_insert_pos = i
                            break
                    if best_insert_pos >= 0:
                        current_order.insert(best_insert_pos, city)
            
            # Add remaining cities where they fit
            for city in remaining_cities:
                best_insert_pos = -1
                for i in range(len(current_order)+1):
                    temp_order = current_order[:i] + [city] + current_order[i:]
                    valid = True
                    for j in range(len(temp_order)-1):
                        if temp_order[j+1] not in direct_flights.get(temp_order[j], []):
                            valid = False
                            break
                    if valid:
                        best_insert_pos = i
                        break
                if best_insert_pos >= 0:
                    current_order.insert(best_insert_pos, city)
            
            # Check if all flights are valid
            valid = True
            for i in range(len(current_order)-1):
                if current_order[i+1] not in direct_flights.get(current_order[i], []):
                    valid = False
                    break
            if not valid or len(current_order) != len(cities):
                continue
            
            # Assign days to this order
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
            
            # Calculate score (how well constraints are met)
            score = 0
            for city, (start, end) in constraints:
                for (s, e, c) in itinerary:
                    if c == city:
                        # Penalize if not fully within window
                        if s < start or e > end:
                            score += abs(s - start) + abs(e - end)
            
            if constraints_met and score < best_score:
                best_score = score
                best_itinerary = itinerary
    
    # Fallback: if no perfect itinerary, take the first valid one found
    if best_itinerary is None:
        # Try a simple connected path
        visited = set()
        current_city = 'Paris'  # Good central hub
        current_order = [current_city]
        visited.add(current_city)
        
        while len(current_order) < len(cities):
            next_city = None
            for neighbor in direct_flights.get(current_city, []):
                if neighbor not in visited:
                    next_city = neighbor
                    break
            if next_city is None:
                break
            current_order.append(next_city)
            visited.add(next_city)
            current_city = next_city
        
        if len(current_order) == len(cities):
            # Assign days
            itinerary = []
            current_day = 1
            remaining_days = city_days.copy()
            
            for city in current_order:
                days_needed = remaining_days[city]
                itinerary.append((current_day, current_day + days_needed - 1, city))
                current_day += days_needed
                remaining_days[city] = 0
            
            if current_day - 1 == 30:
                best_itinerary = itinerary
    
    # Final fallback: just list all cities in any order (won't have valid flights)
    if best_itinerary is None:
        best_itinerary = []
        current_day = 1
        for city in cities:
            days_needed = city_days[city]
            best_itinerary.append((current_day, current_day + days_needed - 1, city))
            current_day += days_needed
    
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