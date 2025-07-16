import json
from collections import defaultdict

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Warsaw': 4,
        'Venice': 3,
        'Vilnius': 3,
        'Salzburg': 4,
        'Amsterdam': 2,
        'Barcelona': 5,
        'Paris': 2,
        'Hamburg': 4,
        'Florence': 5,
        'Tallinn': 2
    }
    
    # Define fixed constraints
    constraints = [
        ('Paris', 1, 2),        # Days 1-2: Paris
        ('Barcelona', 2, 6),     # Days 2-6: Barcelona
        ('Tallinn', 11, 12),     # Days 11-12: Tallinn
        ('Hamburg', 19, 22),     # Days 19-22: Hamburg
        ('Salzburg', 22, 25)     # Days 22-25: Salzburg
    ]
    
    # Define flight connections (undirected graph)
    flights = {
        'Paris': ['Barcelona', 'Amsterdam', 'Hamburg', 'Venice', 'Warsaw', 'Tallinn', 'Vilnius', 'Florence'],
        'Barcelona': ['Paris', 'Amsterdam', 'Hamburg', 'Venice', 'Warsaw', 'Tallinn', 'Florence'],
        'Amsterdam': ['Paris', 'Barcelona', 'Hamburg', 'Venice', 'Warsaw', 'Tallinn', 'Vilnius', 'Florence'],
        'Warsaw': ['Paris', 'Barcelona', 'Amsterdam', 'Venice', 'Hamburg', 'Tallinn', 'Vilnius'],
        'Venice': ['Paris', 'Barcelona', 'Amsterdam', 'Warsaw', 'Hamburg', 'Florence'],
        'Hamburg': ['Paris', 'Barcelona', 'Amsterdam', 'Warsaw', 'Venice', 'Salzburg'],
        'Tallinn': ['Paris', 'Barcelona', 'Amsterdam', 'Warsaw', 'Vilnius'],
        'Florence': ['Paris', 'Barcelona', 'Amsterdam', 'Venice'],
        'Vilnius': ['Paris', 'Amsterdam', 'Warsaw', 'Tallinn'],
        'Salzburg': ['Hamburg']
    }
    
    # Initialize itinerary with fixed constraints
    itinerary = [None] * 25
    for city, start, end in constraints:
        for day in range(start-1, end):
            itinerary[day] = city
    
    # Calculate remaining days needed for each city
    remaining_days = cities.copy()
    for city in cities:
        count = sum(1 for day in itinerary if day == city)
        remaining_days[city] -= count
        if remaining_days[city] < 0:
            return {"itinerary": []}  # Over-allocated
        if remaining_days[city] == 0:
            del remaining_days[city]
    
    # Get all flexible days (None in itinerary)
    flexible_days = [i for i, city in enumerate(itinerary) if city is None]
    
    # We'll use a backtracking approach to fill the flexible days
    def backtrack(index):
        if index == len(flexible_days):
            return True
        
        day = flexible_days[index]
        prev_city = itinerary[day-1] if day > 0 else None
        next_city = itinerary[day+1] if day < 24 else None
        
        # Try all possible cities that have remaining days
        for city in remaining_days:
            if remaining_days[city] <= 0:
                continue
                
            # Check connectivity
            if prev_city and prev_city != city and city not in flights[prev_city]:
                continue
            if next_city and next_city != city and city not in flights[next_city]:
                continue
                
            # Try this city
            itinerary[day] = city
            remaining_days[city] -= 1
            if remaining_days[city] == 0:
                del remaining_days[city]
            
            if backtrack(index + 1):
                return True
            
            # Backtrack
            itinerary[day] = None
            remaining_days[city] = remaining_days.get(city, 0) + 1
        
        return False
    
    if not backtrack(0):
        return {"itinerary": []}
    
    # Verify all days are filled and constraints are met
    if None in itinerary or sum(cities.values()) != 25:
        return {"itinerary": []}
    
    # Group consecutive days in the same city
    grouped_itinerary = []
    current_place = itinerary[0]
    start_day = 1
    for i in range(1, len(itinerary)):
        if itinerary[i] == current_place:
            continue
        else:
            end_day = i
            if start_day == end_day:
                grouped_itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
            else:
                grouped_itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': current_place})
            current_place = itinerary[i]
            start_day = i + 1
    # Add last segment
    if start_day <= 25:
        if start_day == 25:
            grouped_itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
        else:
            grouped_itinerary.append({'day_range': f'Day {start_day}-25', 'place': current_place})
    
    return {"itinerary": grouped_itinerary}

# Run the function and print the result as JSON
result = find_itinerary()
print(json.dumps(result))