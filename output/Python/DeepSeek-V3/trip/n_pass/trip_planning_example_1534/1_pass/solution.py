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
    
    # Define constraints
    constraints = [
        ('Salzburg', 22, 25),
        ('Barcelona', 2, 6),
        ('Paris', 1, 2),
        ('Hamburg', 19, 22),
        ('Tallinn', 11, 12)
    ]
    
    # Define direct flights (undirected graph)
    flights = {
        'Paris': ['Venice', 'Hamburg', 'Vilnius', 'Amsterdam', 'Florence', 'Warsaw', 'Tallinn', 'Barcelona'],
        'Barcelona': ['Amsterdam', 'Warsaw', 'Hamburg', 'Florence', 'Venice', 'Tallinn'],
        'Amsterdam': ['Warsaw', 'Vilnius', 'Hamburg', 'Venice', 'Tallinn', 'Florence'],
        'Warsaw': ['Venice', 'Vilnius', 'Hamburg', 'Tallinn'],
        'Venice': ['Hamburg'],
        'Hamburg': ['Salzburg'],
        'Tallinn': ['Vilnius']
    }
    
    # Correct city name typos in flights
    flights_corrected = {}
    for city, destinations in flights.items():
        corrected_dests = []
        for dest in destinations:
            if dest == 'Amsterdam':
                corrected_dests.append('Amsterdam')
            elif dest == 'Warsaw':
                corrected_dests.append('Warsaw')
            elif dest == 'Hamburg':
                corrected_dests.append('Hamburg')
            elif dest == 'Vilnius':
                corrected_dests.append('Vilnius')
            elif dest == 'Florence':
                corrected_dests.append('Florence')
            elif dest == 'Tallinn':
                corrected_dests.append('Tallinn')
            elif dest == 'Venice':
                corrected_dests.append('Venice')
            elif dest == 'Salzburg':
                corrected_dests.append('Salzburg')
            elif dest == 'Barcelona':
                corrected_dests.append('Barcelona')
            elif dest == 'Paris':
                corrected_dests.append('Paris')
        flights_corrected[city] = corrected_dests
    
    flights = flights_corrected
    
    # Ensure all cities are in flights (some might be missing)
    for city in cities:
        if city not in flights:
            flights[city] = []
    
    # Add reverse flights
    flight_graph = {}
    for city in flights:
        flight_graph[city] = flights[city]
    
    for city in list(flights.keys()):
        for dest in flights[city]:
            if city not in flight_graph[dest]:
                flight_graph[dest].append(city)
    
    # Now perform a backtracking search to find a valid itinerary
    def backtrack(current_itinerary, remaining_cities, day):
        if day > 25:
            if not remaining_cities and all(
                current_itinerary[i]['place'] == city 
                for (city, start, end) in constraints 
                for i in range(start-1, end)
            ):
                return current_itinerary
            return None
        
        # Check constraints for current day
        for (city, start, end) in constraints:
            if start <= day <= end:
                if day == start:
                    # Must be in this city from start to end
                    # Check if we can be in this city
                    if city not in flight_graph.get(current_itinerary[-1]['place'], []):
                        return None
                    # Allocate days from start to end
                    new_itinerary = current_itinerary.copy()
                    for d in range(start, end+1):
                        new_itinerary.append({'day_range': f'Day {d}', 'place': city})
                    remaining = remaining_cities.copy()
                    if city in remaining:
                        remaining[city] -= (end - start + 1)
                        if remaining[city] <= 0:
                            del remaining[city]
                    return backtrack(new_itinerary, remaining, end+1)
        
        # Try all possible next cities
        last_city = current_itinerary[-1]['place'] if current_itinerary else None
        possible_cities = []
        if last_city is None:
            # Start with Paris (due to workshop on day 1-2)
            possible_cities = ['Paris']
        else:
            possible_cities = flight_graph[last_city]
        
        for city in possible_cities:
            if city in remaining_cities:
                new_remaining = remaining_cities.copy()
                new_remaining[city] -= 1
                if new_remaining[city] <= 0:
                    del new_remaining[city]
                new_itinerary = current_itinerary.copy()
                new_itinerary.append({'day_range': f'Day {day}', 'place': city})
                result = backtrack(new_itinerary, new_remaining, day + 1)
                if result is not None:
                    return result
        return None
    
    # Start with Paris on day 1 (due to workshop constraint)
    initial_itinerary = [{'day_range': 'Day 1', 'place': 'Paris'}]
    remaining_cities = cities.copy()
    remaining_cities['Paris'] -= 1
    if remaining_cities['Paris'] == 0:
        del remaining_cities['Paris']
    
    itinerary = backtrack(initial_itinerary, remaining_cities, 2)
    
    if itinerary is None:
        return {"itinerary": []}
    
    # Group consecutive days in the same city
    grouped_itinerary = []
    current_place = itinerary[0]['place']
    start_day = 1
    for i in range(1, len(itinerary)):
        if itinerary[i]['place'] == current_place:
            continue
        else:
            end_day = i
            if start_day == end_day:
                grouped_itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
            else:
                grouped_itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': current_place})
            current_place = itinerary[i]['place']
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