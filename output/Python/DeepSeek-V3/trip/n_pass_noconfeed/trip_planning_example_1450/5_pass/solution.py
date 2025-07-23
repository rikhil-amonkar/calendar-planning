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
    krakow_days = (5, 9)  # Must be exactly days 5-9
    istanbul_end_day = 29  # Must end exactly on day 29
    
    # We'll use a backtracking approach with better constraint handling
    def backtrack(current_itinerary, remaining_cities, current_city, current_day):
        if not remaining_cities:
            # All cities visited
            return current_itinerary
        
        # Try to visit cities that have direct flights from current city
        for next_city in direct_flights.get(current_city, []):
            if next_city not in remaining_cities:
                continue
                
            required_days = cities[next_city]
            
            # Handle special constraints
            if next_city == 'Krakow':
                # Must be exactly days 5-9
                if current_day > 5:
                    continue  # Can't start Krakow after day 5
                if current_day < 5:
                    # Need to wait until day 5
                    wait_days = 5 - current_day
                    new_day = current_day + wait_days
                    if new_day + required_days - 1 > 32:
                        continue
                    # Add waiting period if needed
                    if wait_days > 0:
                        new_itinerary = current_itinerary + [{
                            'day_range': f'Day {current_day}-{new_day-1}',
                            'place': 'Waiting',
                            'days': wait_days
                        }]
                    else:
                        new_itinerary = current_itinerary.copy()
                    
                    # Add Krakow visit
                    new_itinerary += [{
                        'day_range': f'Day {new_day}-{new_day+required_days-1}',
                        'place': next_city,
                        'days': required_days
                    }]
                    new_remaining = remaining_cities.copy()
                    new_remaining.remove(next_city)
                    result = backtrack(new_itinerary, new_remaining, next_city, new_day + required_days)
                    if result:
                        return result
                    continue
                
            elif next_city == 'Istanbul':
                # Must end exactly on day 29
                start_day = istanbul_end_day - required_days + 1
                if start_day < current_day:
                    continue  # Can't start before current day
                if start_day > 32 - required_days + 1:
                    continue  # Would go beyond 32 days
                
                # Add waiting period if needed
                if start_day > current_day:
                    wait_days = start_day - current_day
                    new_itinerary = current_itinerary + [{
                        'day_range': f'Day {current_day}-{start_day-1}',
                        'place': 'Waiting',
                        'days': wait_days
                    }]
                else:
                    new_itinerary = current_itinerary.copy()
                
                # Add Istanbul visit
                new_itinerary += [{
                    'day_range': f'Day {start_day}-{istanbul_end_day}',
                    'place': next_city,
                    'days': required_days
                }]
                new_remaining = remaining_cities.copy()
                new_remaining.remove(next_city)
                result = backtrack(new_itinerary, new_remaining, next_city, istanbul_end_day + 1)
                if result:
                    return result
                continue
                
            else:
                # Regular city - visit immediately for required days
                if current_day + required_days - 1 > 32:
                    continue
                
                new_itinerary = current_itinerary + [{
                    'day_range': f'Day {current_day}-{current_day+required_days-1}',
                    'place': next_city,
                    'days': required_days
                }]
                new_remaining = remaining_cities.copy()
                new_remaining.remove(next_city)
                result = backtrack(new_itinerary, new_remaining, next_city, current_day + required_days)
                if result:
                    return result
        
        return None
    
    # Start with cities that have many connections
    for start_city in ['Frankfurt', 'Munich', 'Hamburg', 'Oslo', 'Stockholm']:
        remaining_cities = set(cities.keys())
        remaining_cities.remove(start_city)
        
        # Add initial city visit (1 day to start)
        initial_days = min(cities[start_city], 1)
        itinerary = [{
            'day_range': f'Day 1-{initial_days}',
            'place': start_city,
            'days': initial_days
        }]
        
        result = backtrack(
            current_itinerary=itinerary,
            remaining_cities=remaining_cities,
            current_city=start_city,
            current_day=initial_days + 1
        )
        
        if result:
            # Verify all requirements are met
            day_counts = defaultdict(int)
            for entry in result:
                if entry['place'] != 'Waiting':
                    place = entry['place']
                    day_counts[place] += entry['days']
            
            if all(day_counts[city] == cities[city] for city in cities):
                # Verify flight connections
                valid = True
                prev_place = None
                for entry in result:
                    if entry['place'] == 'Waiting':
                        continue
                    if prev_place and entry['place'] not in direct_flights.get(prev_place, []):
                        valid = False
                        break
                    prev_place = entry['place']
                
                if valid:
                    # Verify special constraints
                    krakow_ok = False
                    istanbul_ok = False
                    for entry in result:
                        if entry['place'] == 'Krakow':
                            start, end = map(int, [entry['day_range'].split('-')[0][4:], entry['day_range'].split('-')[1][4:]])
                            if start == 5 and end == 9:
                                krakow_ok = True
                        if entry['place'] == 'Istanbul':
                            end_day = int(entry['day_range'].split('-')[1][4:])
                            if end_day == 29:
                                istanbul_ok = True
                    
                    if krakow_ok and istanbul_ok:
                        # Format the final itinerary
                        final_itinerary = []
                        for entry in result:
                            if entry['place'] != 'Waiting':
                                final_itinerary.append({
                                    'day_range': entry['day_range'],
                                    'place': entry['place']
                                })
                        return {'itinerary': final_itinerary}
    
    return {'itinerary': []}

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))