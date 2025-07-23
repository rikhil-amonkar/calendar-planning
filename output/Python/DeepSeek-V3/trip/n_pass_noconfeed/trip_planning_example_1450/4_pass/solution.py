import json
from collections import defaultdict

def find_itinerary():
    # Define cities and required days
    cities = {
        'Stockholm': 3,
        'Hamburg': 5,
        'Florence': 2,
        'Istanbul': 5,
        'Oslo': 5,
        'Vilnius': 5,
        'Santorini': 2,
        'Munich': 5,
        'Frankfurt': 4,
        'Krakow': 5
    }
    
    # Direct flights
    direct_flights = {
        'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Vilnius', 'Frankfurt', 'Hamburg', 'Munich'],
        'Stockholm': ['Oslo', 'Istanbul', 'Munich', 'Hamburg', 'Santorini', 'Krakow', 'Frankfurt'],
        'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Oslo', 'Munich', 'Stockholm'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Florence', 'Stockholm', 'Munich', 'Hamburg', 'Vilnius'],
        'Istanbul': ['Krakow', 'Oslo', 'Stockholm', 'Vilnius', 'Frankfurt', 'Munich', 'Hamburg'],
        'Vilnius': ['Krakow', 'Istanbul', 'Oslo', 'Frankfurt', 'Munich'],
        'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Frankfurt', 'Florence', 'Krakow', 'Vilnius'],
        'Hamburg': ['Stockholm', 'Munich', 'Istanbul', 'Frankfurt', 'Oslo'],
        'Florence': ['Frankfurt', 'Munich'],
        'Santorini': ['Stockholm', 'Oslo']
    }
    
    # Special constraints
    krakow_days = (5, 9)  # Must be days 5-9
    istanbul_end_day = 29  # Must end on day 29
    
    # We'll use a backtracking approach with better constraint handling
    def backtrack(current_itinerary, remaining_days, current_city, visited_cities, current_day):
        if len(visited_cities) == len(cities):
            # All cities visited
            return current_itinerary
        
        # Try to visit cities that have direct flights from current city
        for next_city in direct_flights.get(current_city, []):
            if next_city not in visited_cities and remaining_days[next_city] > 0:
                required_days = cities[next_city]
                
                # Handle special constraints
                if next_city == 'Krakow':
                    # Must be days 5-9
                    if current_day > 5:
                        continue  # Too late to visit Krakow
                    stay_days = 5
                    start_day = 5
                    end_day = 9
                elif next_city == 'Istanbul':
                    # Must end on day 29
                    if current_day + required_days - 1 > istanbul_end_day:
                        continue  # Can't end on day 29
                    if current_day + required_days - 1 < istanbul_end_day:
                        continue  # Can't end before day 29
                    stay_days = 5
                    start_day = istanbul_end_day - stay_days + 1
                    end_day = istanbul_end_day
                else:
                    # Regular city - stay as many days as required
                    stay_days = min(required_days, 32 - current_day)
                    start_day = current_day
                    end_day = start_day + stay_days - 1
                
                # Check if this would exceed total trip days
                if end_day > 32:
                    continue
                
                # Check if we have enough days left to visit this city
                if stay_days < cities[next_city]:
                    continue
                
                # Update itinerary and remaining days
                new_itinerary = current_itinerary + [{
                    'day_range': f'Day {start_day}-{end_day}',
                    'place': next_city,
                    'days': stay_days
                }]
                new_remaining = remaining_days.copy()
                new_remaining[next_city] = 0  # Mark as fully visited
                new_visited = visited_cities.copy()
                new_visited.add(next_city)
                
                # Recursively continue from next city
                result = backtrack(new_itinerary, new_remaining, next_city, new_visited, end_day + 1)
                if result:
                    return result
        
        return None
    
    # Try starting with cities that have many connections
    for start_city in ['Frankfurt', 'Munich', 'Hamburg', 'Oslo', 'Stockholm']:
        if cities[start_city] >= 4:
            remaining_days = cities.copy()
            itinerary = backtrack(
                current_itinerary=[],
                remaining_days=remaining_days,
                current_city=start_city,
                visited_cities=set(),
                current_day=1
            )
            
            if itinerary:
                # Verify all requirements are met
                day_counts = defaultdict(int)
                for entry in itinerary:
                    place = entry['place']
                    day_counts[place] += entry['days']
                
                if all(day_counts[city] == cities[city] for city in cities):
                    # Verify flight connections
                    valid = True
                    for i in range(len(itinerary)-1):
                        current = itinerary[i]['place']
                        next_place = itinerary[i+1]['place']
                        if next_place not in direct_flights.get(current, []):
                            valid = False
                            break
                    
                    if valid:
                        # Verify special constraints
                        krakow_ok = True
                        istanbul_ok = True
                        for entry in itinerary:
                            if entry['place'] == 'Krakow':
                                start, end = map(int, entry['day_range'].split('-')[0][4:], entry['day_range'].split('-')[1][4:])
                                if not (start <= 5 and end >= 9):
                                    krakow_ok = False
                            if entry['place'] == 'Istanbul':
                                end_day = int(entry['day_range'].split('-')[1][4:])
                                if end_day != 29:
                                    istanbul_ok = False
                        
                        if krakow_ok and istanbul_ok:
                            return {'itinerary': [{'day_range': entry['day_range'], 'place': entry['place']} for entry in itinerary]}
    
    return {'itinerary': []}

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))