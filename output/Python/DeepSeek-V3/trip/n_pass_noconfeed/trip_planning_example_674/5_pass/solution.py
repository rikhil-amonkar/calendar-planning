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
        for i in range(len(sequence) - 1):
            current = sequence[i]
            next_city = sequence[i + 1]
            if next_city not in flight_routes[current]:
                return False
        return True
    
    def satisfies_constraints(day_assignments):
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
    
    # First assign constrained cities to their required days
    day_assignments = {}
    for city in cities:
        for (start, end) in cities[city]['constraints']:
            duration = cities[city]['days']
            # Find a block of 'duration' days within the constraint range
            for day in range(start, end - duration + 2):
                valid = True
                for d in range(day, day + duration):
                    if d in day_assignments:
                        valid = False
                        break
                if valid:
                    for d in range(day, day + duration):
                        day_assignments[d] = city
                    break
            else:
                return {"itinerary": []}  # Couldn't satisfy constraints
    
    # Now assign remaining cities to available days
    remaining_cities = [city for city in cities if city not in day_assignments.values()]
    
    # Try all permutations of remaining cities
    for city_order in permutations(remaining_cities):
        temp_assignments = day_assignments.copy()
        current_day = 1
        valid = True
        
        for city in city_order:
            duration = cities[city]['days']
            # Find next available block of days
            while current_day <= 14:
                # Check if current_day is available and we have enough consecutive days
                available = True
                for d in range(current_day, current_day + duration):
                    if d > 14 or d in temp_assignments:
                        available = False
                        break
                
                if available:
                    for d in range(current_day, current_day + duration):
                        temp_assignments[d] = city
                    current_day += duration
                    break
                else:
                    current_day += 1
            else:
                valid = False
                break
        
        if valid:
            # Now check flight connections
            # Get the sequence of cities in order of days
            sequence = []
            day = 1
            while day <= 14:
                if day in temp_assignments:
                    city = temp_assignments[day]
                    sequence.append(city)
                    day += cities[city]['days']
                else:
                    day += 1
            
            if is_valid_sequence(sequence):
                # Build the itinerary
                itinerary = []
                day = 1
                while day <= 14:
                    if day in temp_assignments:
                        city = temp_assignments[day]
                        duration = cities[city]['days']
                        end_day = day + duration - 1
                        itinerary.append({
                            'day_range': f"Day {day}-{end_day}",
                            'place': city
                        })
                        day = end_day + 1
                    else:
                        day += 1
                
                return {"itinerary": itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))