import json
from itertools import permutations

def find_itinerary():
    # Input constraints
    total_days = 13
    seville_days = 2
    stuttgart_days = 7
    porto_days = 3
    madrid_days = 4
    conference_days = [7, 13]
    madrid_relatives_range = (1, 4)
    
    # Direct flights
    direct_flights = {
        'Porto': ['Stuttgart', 'Seville', 'Madrid'],
        'Seville': ['Porto', 'Madrid'],
        'Madrid': ['Porto', 'Seville'],
        'Stuttgart': ['Porto']
    }
    
    cities = ['Seville', 'Stuttgart', 'Porto', 'Madrid']
    
    # Generate all possible permutations of the 4 cities
    for perm in permutations(cities):
        itinerary = []
        current_city = None
        remaining_days = {
            'Seville': seville_days,
            'Stuttgart': stuttgart_days,
            'Porto': porto_days,
            'Madrid': madrid_days
        }
        day = 1
        
        # Try to build itinerary with this permutation
        valid = True
        for city in perm:
            if current_city is None:
                # Start with the first city in permutation
                current_city = city
            else:
                # Check if flight is possible
                if city not in direct_flights[current_city]:
                    valid = False
                    break
                # Transition day (counts for both cities)
                itinerary.append({
                    'day_range': f"Day {day}",
                    'place': f"{current_city} to {city}"
                })
                remaining_days[current_city] -= 1
                remaining_days[city] -= 1
                day += 1
                current_city = city
            
            # Stay in current city as long as possible
            stay_days = remaining_days[current_city]
            if stay_days > 0:
                start_day = day
                end_day = day + stay_days - 1
                itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': current_city
                })
                day = end_day + 1
                remaining_days[current_city] = 0
        
        # Check if all days are allocated and constraints are met
        if valid and day - 1 == total_days:
            # Check conference days in Stuttgart
            stuttgart_days_in_itinerary = []
            for entry in itinerary:
                if entry['place'] == 'Stuttgart':
                    day_range = entry['day_range']
                    if '-' in day_range:
                        start, end = map(int, day_range.split('Day ')[1].split('-'))
                        stuttgart_days_in_itinerary.extend(range(start, end + 1))
                    else:
                        day_num = int(day_range.split('Day ')[1])
                        stuttgart_days_in_itinerary.append(day_num)
            
            # Check if all conference days are in Stuttgart
            if all(conf_day in stuttgart_days_in_itinerary for conf_day in conference_days):
                # Check Madrid relatives constraint
                madrid_days_in_itinerary = []
                for entry in itinerary:
                    if entry['place'] == 'Madrid':
                        day_range = entry['day_range']
                        if '-' in day_range:
                            start, end = map(int, day_range.split('Day ')[1].split('-'))
                            madrid_days_in_itinerary.extend(range(start, end + 1))
                        else:
                            day_num = int(day_range.split('Day ')[1])
                            madrid_days_in_itinerary.append(day_num)
                
                if any(day in madrid_days_in_itinerary for day in range(madrid_relatives_range[0], madrid_relatives_range[1] + 1)):
                    # Check all days are allocated correctly
                    total_allocated_days = 0
                    for city in cities:
                        total_allocated_days = sum(1 for entry in itinerary if city in entry['place'])
                    if (sum(1 for entry in itinerary if 'Seville' in entry['place']) == seville_days and
                        sum(1 for entry in itinerary if 'Stuttgart' in entry['place']) == stuttgart_days and
                        sum(1 for entry in itinerary if 'Porto' in entry['place']) == porto_days and
                        sum(1 for entry in itinerary if 'Madrid' in entry['place']) == madrid_days):
                        return {'itinerary': itinerary}
    
    # If no valid itinerary found (shouldn't happen with given constraints)
    return {'itinerary': []}

# Find and print the itinerary
result = find_itinerary()
print(json.dumps(result))