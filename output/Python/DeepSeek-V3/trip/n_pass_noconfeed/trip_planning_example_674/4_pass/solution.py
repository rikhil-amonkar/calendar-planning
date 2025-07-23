import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Helsinki': {'days': 2, 'constraints': [(1, 2)]},
        'Warsaw': {'days': 3, 'constraints': [(9, 11)]},
        'Madrid': {'days': 4, 'constraints': []},
        'Split': {'days': 4, 'constraints': []},
        'Reykjavik': {'days': 2, 'constraints': [(8, 9)]},
        'Budapest': {'days': 4, 'constraints': []}
    }
    
    flight_routes = {
        'Helsinki': ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw'],
        'Reykjavik': ['Helsinki', 'Warsaw', 'Budapest', 'Madrid'],
        'Budapest': ['Warsaw', 'Helsinki', 'Madrid', 'Reykjavik'],
        'Warsaw': ['Budapest', 'Reykjavik', 'Helsinki', 'Madrid', 'Split'],
        'Madrid': ['Split', 'Helsinki', 'Budapest', 'Warsaw'],
        'Split': ['Madrid', 'Helsinki', 'Warsaw']
    }
    
    def is_valid_sequence(sequence):
        # Check flight connections between consecutive cities
        for i in range(len(sequence) - 1):
            current = sequence[i]
            next_city = sequence[i + 1]
            if next_city not in flight_routes[current]:
                return False
        return True
    
    def satisfies_constraints(day_assignments):
        # Check all constraints are satisfied
        for city in cities:
            for (start, end) in cities[city]['constraints']:
                satisfied = False
                for day in range(start, end + 1):
                    if day_assignments.get(day) == city:
                        satisfied = True
                        break
                if not satisfied:
                    return False
        return True
    
    # Generate all possible sequences that have valid flight connections
    all_cities = list(cities.keys())
    constrained_cities = [city for city in cities if cities[city]['constraints']]
    other_cities = [city for city in cities if city not in constrained_cities]
    
    # Try different orders prioritizing constrained cities first
    for constrained_order in permutations(constrained_cities):
        for other_order in permutations(other_cities):
            sequence = list(constrained_order) + list(other_order)
            if not is_valid_sequence(sequence):
                continue
            
            # Try to assign days to this sequence
            days = [None] * 15  # Days 1-14 (index 1-14)
            day_assignments = {}
            current_day = 1
            
            for city in sequence:
                duration = cities[city]['days']
                end_day = current_day + duration - 1
                
                if end_day > 14:
                    break  # Doesn't fit in 14 days
                
                # Check if these days are available
                valid = True
                for day in range(current_day, end_day + 1):
                    if days[day] is not None:
                        valid = False
                        break
                
                if not valid:
                    break
                
                # Assign the days
                for day in range(current_day, end_day + 1):
                    days[day] = city
                    day_assignments[day] = city
                
                current_day = end_day + 1
            
            else:  # All cities assigned successfully
                if satisfies_constraints(day_assignments):
                    # Build the itinerary
                    itinerary = []
                    current_day = 1
                    while current_day <= 14:
                        if days[current_day] is not None:
                            city = days[current_day]
                            duration = cities[city]['days']
                            end_day = current_day + duration - 1
                            itinerary.append({
                                'day_range': f"Day {current_day}-{end_day}",
                                'place': city
                            })
                            current_day = end_day + 1
                        else:
                            current_day += 1
                    
                    return {"itinerary": itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))