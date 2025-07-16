import json
from itertools import permutations

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
    
    # Define constraints - these are fixed periods that must be satisfied
    constraints = [
        ('Paris', 1, 2),        # Days 1-2: Paris (workshop)
        ('Barcelona', 2, 6),     # Days 2-6: Barcelona
        ('Tallinn', 11, 12),     # Days 11-12: Tallinn
        ('Hamburg', 19, 22),     # Days 19-22: Hamburg
        ('Salzburg', 22, 25)     # Days 22-25: Salzburg
    ]
    
    # Define direct flights (undirected graph)
    flights = {
        'Paris': ['Venice', 'Hamburg', 'Vilnius', 'Amsterdam', 'Florence', 'Warsaw', 'Tallinn', 'Barcelona'],
        'Barcelona': ['Amsterdam', 'Warsaw', 'Hamburg', 'Florence', 'Venice', 'Tallinn'],
        'Amsterdam': ['Warsaw', 'Vilnius', 'Hamburg', 'Venice', 'Tallinn', 'Florence'],
        'Warsaw': ['Venice', 'Vilnius', 'Hamburg', 'Tallinn'],
        'Venice': ['Hamburg'],
        'Hamburg': ['Salzburg'],
        'Tallinn': ['Vilnius'],
        'Florence': [],  # Added missing cities
        'Vilnius': [],
        'Salzburg': []
    }
    
    # Correct city name typos in flights
    city_name_mapping = {
        'Venice': 'Venice',
        'Hamburg': 'Hamburg',
        'Florence': 'Florence',
        'Salzburg': 'Salzburg'
    }
    
    flight_graph = {}
    for city, destinations in flights.items():
        corrected_city = city_name_mapping.get(city, city)
        corrected_dests = []
        for dest in destinations:
            corrected_dest = city_name_mapping.get(dest, dest)
            corrected_dests.append(corrected_dest)
        flight_graph[corrected_city] = corrected_dests
    
    # Ensure all cities are in flight_graph
    for city in cities:
        if city not in flight_graph:
            flight_graph[city] = []
    
    # Add reverse flights
    for city in list(flight_graph.keys()):
        for dest in flight_graph[city]:
            if city not in flight_graph[dest]:
                flight_graph[dest].append(city)
    
    # Initialize itinerary with fixed constraints
    itinerary = []
    for day in range(1, 26):
        placed = False
        for (city, start, end) in constraints:
            if start <= day <= end:
                itinerary.append({'day_range': f'Day {day}', 'place': city})
                placed = True
                break
        if not placed:
            itinerary.append({'day_range': f'Day {day}', 'place': None})
    
    # Verify all constraints are properly placed
    for (city, start, end) in constraints:
        for day in range(start, end + 1):
            if itinerary[day - 1]['place'] != city:
                return {"itinerary": []}  # Constraints conflict
    
    # Calculate remaining days needed for each city
    remaining_days = cities.copy()
    for (city, start, end) in constraints:
        duration = end - start + 1
        if city in remaining_days:
            remaining_days[city] -= duration
            if remaining_days[city] < 0:
                return {"itinerary": []}  # Over-allocated
            if remaining_days[city] == 0:
                del remaining_days[city]
    
    # Fill in the flexible days (where place is None)
    def backtrack(current_itinerary, remaining_days, day_idx):
        if day_idx >= 25:
            if not remaining_days:
                return current_itinerary
            return None
        
        # Skip if this day is already constrained
        if current_itinerary[day_idx]['place'] is not None:
            return backtrack(current_itinerary, remaining_days, day_idx + 1)
        
        # Get previous city to check flight connections
        prev_city = current_itinerary[day_idx - 1]['place'] if day_idx > 0 else None
        
        # Try all possible cities that have remaining days and are connected
        possible_cities = []
        if prev_city is None:
            possible_cities = list(remaining_days.keys())
        else:
            possible_cities = [city for city in flight_graph[prev_city] if city in remaining_days]
        
        for city in possible_cities:
            # Try to allocate as many consecutive days as possible
            max_days = min(remaining_days[city], 25 - day_idx)
            for days in range(max_days, 0, -1):
                new_remaining = remaining_days.copy()
                new_remaining[city] -= days
                if new_remaining[city] == 0:
                    del new_remaining[city]
                
                new_itinerary = current_itinerary.copy()
                for d in range(day_idx, day_idx + days):
                    new_itinerary[d]['place'] = city
                
                result = backtrack(new_itinerary, new_remaining, day_idx + days)
                if result is not None:
                    return result
        return None
    
    # Start backtracking from day 1
    result_itinerary = backtrack(itinerary, remaining_days, 0)
    
    if result_itinerary is None:
        return {"itinerary": []}
    
    # Group consecutive days in the same city
    grouped_itinerary = []
    current_place = result_itinerary[0]['place']
    start_day = 1
    for i in range(1, len(result_itinerary)):
        if result_itinerary[i]['place'] == current_place:
            continue
        else:
            end_day = i
            if start_day == end_day:
                grouped_itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
            else:
                grouped_itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': current_place})
            current_place = result_itinerary[i]['place']
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