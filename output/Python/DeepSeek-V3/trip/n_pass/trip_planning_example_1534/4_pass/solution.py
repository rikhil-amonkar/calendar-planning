import json
from collections import defaultdict

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Warsaw': 4,  # Note: Original had 'Warsaw' but flight graph uses 'Warsaw'
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
    
    # Correct city name to match flight graph
    cities['Warsaw'] = cities.pop('Warsaw', cities.pop('Warsaw', 4))
    
    # Define constraints - these are fixed periods that must be satisfied
    constraints = [
        ('Paris', 1, 2),        # Days 1-2: Paris
        ('Barcelona', 2, 6),     # Days 2-6: Barcelona
        ('Tallinn', 11, 12),     # Days 11-12: Tallinn
        ('Hamburg', 19, 22),     # Days 19-22: Hamburg
        ('Salzburg', 22, 25)     # Days 22-25: Salzburg
    ]
    
    # Correct city names in constraints
    constraints = [
        ('Paris', 1, 2),
        ('Barcelona', 2, 6),
        ('Tallinn', 11, 12),
        ('Hamburg', 19, 22),
        ('Salzburg', 22, 25)
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
        'Hamburg': 'Hamburg',
        'Barcelona': 'Barcelona',
        'Florence': 'Florence',
        'Salzburg': 'Salzburg',
        'Vilnius': 'Vilnius',
        'Tallinn': 'Tallinn'
    }
    
    flight_graph = defaultdict(list)
    for city, destinations in flights.items():
        corrected_city = city_name_mapping.get(city, city)
        for dest in destinations:
            corrected_dest = city_name_mapping.get(dest, dest)
            flight_graph[corrected_city].append(corrected_dest)
            flight_graph[corrected_dest].append(corrected_city)  # Add reverse flight
    
    # Initialize itinerary with fixed constraints
    itinerary = [None] * 25
    for (city, start, end) in constraints:
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
    
    # We'll use a greedy approach to fill the flexible days
    current_city = None
    for day in flexible_days:
        if current_city is None:
            # Choose any city with remaining days
            for city in remaining_days:
                current_city = city
                break
        else:
            # Try to stay in current city if possible
            if remaining_days.get(current_city, 0) <= 0:
                current_city = None
                for city in flight_graph[current_city]:
                    if remaining_days.get(city, 0) > 0:
                        current_city = city
                        break
        
        if current_city is None:
            # No valid city found
            return {"itinerary": []}
        
        itinerary[day] = current_city
        remaining_days[current_city] -= 1
        if remaining_days[current_city] == 0:
            del remaining_days[current_city]
            current_city = None
    
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