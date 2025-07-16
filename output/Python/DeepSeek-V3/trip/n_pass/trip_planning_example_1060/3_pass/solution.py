import json
from itertools import permutations

def find_itinerary():
    # Define the cities and their required days
    cities = {
        'Stuttgart': 4,
        'Istanbul': 4,
        'Vilnius': 4,
        'Seville': 3,
        'Geneva': 5,
        'Valencia': 5,
        'Munich': 3,
        'Reykjavik': 4
    }
    
    # Define the flight connections (undirected)
    flights = {
        'Geneva': ['Istanbul', 'Munich', 'Valencia'],
        'Istanbul': ['Geneva', 'Stuttgart', 'Vilnius', 'Valencia', 'Munich'],
        'Reykjavik': ['Munich', 'Stuttgart'],
        'Stuttgart': ['Istanbul', 'Valencia', 'Reykjavik'],
        'Vilnius': ['Istanbul', 'Munich'],
        'Seville': ['Valencia', 'Munich'],
        'Valencia': ['Stuttgart', 'Seville', 'Istanbul', 'Geneva', 'Munich'],
        'Munich': ['Reykjavik', 'Geneva', 'Vilnius', 'Seville', 'Istanbul', 'Valencia']
    }
    
    # Fixed constraints
    fixed_days = {
        'Stuttgart': [(4, 4), (7, 7)],  # Day 4 and 7 must be in Stuttgart
        'Istanbul': [(19, 22)],         # Days 19-22 in Istanbul
        'Munich': [(13, 15)],           # Days 13-15 in Munich
        'Reykjavik': [(1, 4)]           # Days 1-4 in Reykjavik
    }
    
    # Initialize the itinerary
    itinerary = [None] * 25  # Days 1-25 (0-indexed)
    
    # Assign fixed days first
    for city, ranges in fixed_days.items():
        for (start, end) in ranges:
            for day in range(start - 1, end):
                itinerary[day] = city
    
    # Remaining cities to assign: Vilnius, Seville, Geneva, Valencia
    remaining_cities = [city for city in cities if city not in ['Stuttgart', 'Istanbul', 'Munich', 'Reykjavik']]
    remaining_days = {city: cities[city] for city in remaining_cities}
    
    # Find all available slots (contiguous None blocks)
    def find_available_slots(itinerary, length):
        slots = []
        i = 0
        while i < 25:
            if itinerary[i] is None:
                start = i
                while i < 25 and itinerary[i] is None:
                    i += 1
                end = i
                if end - start >= length:
                    slots.append((start, end))
            else:
                i += 1
        return slots
    
    # Try all permutations of remaining cities to find a valid assignment
    for perm in permutations(remaining_cities):
        temp_itinerary = itinerary.copy()
        valid = True
        
        # Try to assign cities in this permutation order
        for city in perm:
            days_needed = remaining_days[city]
            slots = find_available_slots(temp_itinerary, days_needed)
            
            assigned = False
            for start, end in slots:
                if end - start >= days_needed:
                    # Check flight connections before assigning
                    # Check connection with previous day
                    if start > 0 and temp_itinerary[start-1] is not None:
                        if city not in flights.get(temp_itinerary[start-1], []):
                            continue
                    # Check connection with next day (if not last day)
                    if start + days_needed < 25 and temp_itinerary[start + days_needed] is not None:
                        if temp_itinerary[start + days_needed] not in flights.get(city, []):
                            continue
                    
                    # Assign the city
                    for i in range(start, start + days_needed):
                        temp_itinerary[i] = city
                    assigned = True
                    break
            
            if not assigned:
                valid = False
                break
        
        if not valid:
            continue
        
        # Check if all days are filled
        if None in temp_itinerary:
            continue
        
        # Verify all flight connections
        flight_valid = True
        for i in range(24):
            current = temp_itinerary[i]
            next_city = temp_itinerary[i + 1]
            if current != next_city:
                if next_city not in flights.get(current, []):
                    flight_valid = False
                    break
        
        if flight_valid:
            # Convert itinerary to JSON format
            json_itinerary = []
            current_city = temp_itinerary[0]
            start_day = 1
            for i in range(1, 25):
                if temp_itinerary[i] != current_city:
                    json_itinerary.append({
                        'day_range': f'Day {start_day}-{i}',
                        'place': current_city
                    })
                    current_city = temp_itinerary[i]
                    start_day = i + 1
            json_itinerary.append({
                'day_range': f'Day {start_day}-25',
                'place': current_city
            })
            
            return {'itinerary': json_itinerary}
    
    return {'error': 'No valid itinerary found'}

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result))