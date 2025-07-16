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
    
    # Assign remaining days
    # This is a simplified approach; a more robust solution would involve backtracking or constraint satisfaction
    # For simplicity, we'll assign the remaining cities in order
    
    # Assign Geneva (5 days)
    # Find contiguous block of 5 days not assigned
    geneva_assigned = False
    for i in range(25):
        if itinerary[i] is None:
            if i + 5 <= 25 and all(itinerary[j] is None for j in range(i, i + 5)):
                for j in range(i, i + 5):
                    itinerary[j] = 'Geneva'
                geneva_assigned = True
                break
    if not geneva_assigned:
        return None
    
    # Assign Valencia (5 days)
    valencia_assigned = False
    for i in range(25):
        if itinerary[i] is None:
            if i + 5 <= 25 and all(itinerary[j] is None for j in range(i, i + 5)):
                for j in range(i, i + 5):
                    itinerary[j] = 'Valencia'
                valencia_assigned = True
                break
    if not valencia_assigned:
        return None
    
    # Assign Vilnius (4 days)
    vilnius_assigned = False
    for i in range(25):
        if itinerary[i] is None:
            if i + 4 <= 25 and all(itinerary[j] is None for j in range(i, i + 4)):
                for j in range(i, i + 4):
                    itinerary[j] = 'Vilnius'
                vilnius_assigned = True
                break
    if not vilnius_assigned:
        return None
    
    # Assign Seville (3 days)
    seville_assigned = False
    for i in range(25):
        if itinerary[i] is None:
            if i + 3 <= 25 and all(itinerary[j] is None for j in range(i, i + 3)):
                for j in range(i, i + 3):
                    itinerary[j] = 'Seville'
                seville_assigned = True
                break
    if not seville_assigned:
        return None
    
    # Check if all days are assigned
    if None in itinerary:
        return None
    
    # Verify flight connections
    for i in range(24):
        current = itinerary[i]
        next_city = itinerary[i + 1]
        if current != next_city:
            if next_city not in flights.get(current, []):
                return None
    
    # Convert itinerary to JSON format
    json_itinerary = []
    current_city = itinerary[0]
    start_day = 1
    for i in range(1, 25):
        if itinerary[i] != current_city:
            json_itinerary.append({
                'day_range': f'Day {start_day}-{i}',
                'place': current_city
            })
            current_city = itinerary[i]
            start_day = i + 1
    json_itinerary.append({
        'day_range': f'Day {start_day}-25',
        'place': current_city
    })
    
    return {'itinerary': json_itinerary}

# Run the function and print the result
result = find_itinerary()
if result:
    print(json.dumps(result))
else:
    print(json.dumps({'error': 'No valid itinerary found'}))