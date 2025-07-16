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
                    'day': day,
                    'place': f"{current_city} to {city}",
                    'type': 'travel'
                })
                remaining_days[current_city] -= 1
                remaining_days[city] -= 1
                day += 1
                current_city = city
            
            # Stay in current city as long as possible
            stay_days = remaining_days[current_city]
            if stay_days > 0:
                itinerary.append({
                    'day': day,
                    'place': current_city,
                    'type': 'stay',
                    'duration': stay_days
                })
                day += stay_days
                remaining_days[current_city] = 0
        
        # Check if all days are allocated and constraints are met
        if valid and day - 1 == total_days:
            # Check conference days in Stuttgart
            stuttgart_days_in_itinerary = []
            for entry in itinerary:
                if entry['place'] == 'Stuttgart' and entry['type'] == 'stay':
                    stuttgart_days_in_itinerary.extend(range(entry['day'], entry['day'] + entry['duration']))
            
            # Check if all conference days are in Stuttgart
            if all(conf_day in stuttgart_days_in_itinerary for conf_day in conference_days):
                # Check Madrid relatives constraint
                madrid_days_in_itinerary = []
                for entry in itinerary:
                    if entry['place'] == 'Madrid' and entry['type'] == 'stay':
                        madrid_days_in_itinerary.extend(range(entry['day'], entry['day'] + entry['duration']))
                
                if any(day in madrid_days_in_itinerary for day in range(madrid_relatives_range[0], madrid_relatives_range[1] + 1)):
                    # Check all days are allocated correctly
                    allocated_days = {
                        'Seville': 0,
                        'Stuttgart': 0,
                        'Porto': 0,
                        'Madrid': 0
                    }
                    for entry in itinerary:
                        if entry['type'] == 'stay':
                            allocated_days[entry['place']] += entry['duration']
                        else:
                            cities = entry['place'].split(' to ')
                            allocated_days[cities[0]] += 1
                            allocated_days[cities[1]] += 1
                    
                    if (allocated_days['Seville'] == seville_days and
                        allocated_days['Stuttgart'] == stuttgart_days and
                        allocated_days['Porto'] == porto_days and
                        allocated_days['Madrid'] == madrid_days):
                        # Format the itinerary for output
                        formatted_itinerary = []
                        current_day = 1
                        for entry in itinerary:
                            if entry['type'] == 'stay':
                                if entry['duration'] == 1:
                                    formatted_itinerary.append({
                                        'day_range': f"Day {entry['day']}",
                                        'place': entry['place']
                                    })
                                else:
                                    formatted_itinerary.append({
                                        'day_range': f"Day {entry['day']}-{entry['day'] + entry['duration'] - 1}",
                                        'place': entry['place']
                                    })
                            else:
                                formatted_itinerary.append({
                                    'day_range': f"Day {entry['day']}",
                                    'place': entry['place']
                                })
                        return {'itinerary': formatted_itinerary}
    
    # If no valid itinerary found (shouldn't happen with given constraints)
    return {'itinerary': []}

# Find and print the itinerary
result = find_itinerary()
print(json.dumps(result, indent=2))