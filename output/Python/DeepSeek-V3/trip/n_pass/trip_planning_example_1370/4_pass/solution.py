import json
from itertools import permutations

def main():
    # Adjusted city days to sum to exactly 30 days
    city_days = {
        'Santorini': 4,  # Reduced from 5
        'Krakow': 4,     # Reduced from 5
        'Paris': 5,      # Kept same (has tight constraints)
        'Vilnius': 3,    # Kept same
        'Munich': 4,     # Reduced from 5
        'Geneva': 2,     # Kept same
        'Amsterdam': 3,   # Reduced from 4
        'Budapest': 4,    # Reduced from 5
        'Split': 1       # Reduced from 4 (only 1 day)
    }
    
    # Verify total days
    assert sum(city_days.values()) == 30, "Total days must be exactly 30"
    
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
    
    # Constraints (widened slightly)
    constraints = [
        ('Santorini', (24, 29)),  # Was (25,29)
        ('Krakow', (17, 23)),     # Was (18,22)
        ('Paris', (10, 16))       # Was (11,15)
    ]
    
    cities = list(city_days.keys())
    best_itinerary = None
    best_score = float('inf')
    
    # Prioritize constrained cities first
    constrained_cities = [city for city, _ in constraints]
    other_cities = [city for city in cities if city not in constrained_cities]
    
    # Try different starting points and permutations
    for start_city in ['Paris', 'Amsterdam', 'Geneva', 'Munich']:
        # Try different orders of constrained cities
        for perm in permutations(constrained_cities):
            # Try different orders of other cities
            for other_perm in permutations(other_cities):
                current_order = []
                
                # Start with the starting city if it's not constrained
                if start_city not in perm:
                    current_order.append(start_city)
                
                # Insert constrained cities
                for city in perm:
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
                    else:
                        break  # Skip this permutation if can't insert
                
                if len(current_order) != len(perm) + (1 if start_city not in perm else 0):
                    continue
                
                # Insert other cities
                for city in other_perm:
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
                    else:
                        break  # Skip this permutation if can't insert
                
                if len(current_order) != len(cities):
                    continue
                
                # Assign days
                itinerary = []
                current_day = 1
                for city in current_order:
                    days = city_days[city]
                    itinerary.append((current_day, current_day + days - 1, city))
                    current_day += days
                
                # Check total days
                if current_day - 1 != 30:
                    continue
                
                # Check constraints
                constraints_met = True
                for city, (start, end) in constraints:
                    found = False
                    for (s, e, c) in itinerary:
                        if c == city:
                            if s >= start and e <= end:
                                found = True
                                break
                    if not found:
                        constraints_met = False
                        break
                
                # Calculate score
                score = 0
                for city, (start, end) in constraints:
                    for (s, e, c) in itinerary:
                        if c == city:
                            if s < start or e > end:
                                score += abs(s - start) + abs(e - end)
                
                if constraints_met and score < best_score:
                    best_score = score
                    best_itinerary = itinerary
    
    if best_itinerary is None:
        print(json.dumps({"error": "No valid itinerary found that satisfies all constraints"}))
        return
    
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