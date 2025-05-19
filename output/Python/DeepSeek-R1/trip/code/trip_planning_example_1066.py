import itertools
import json

cities = {
    'Brussels': 4,
    'Bucharest': 3,
    'Stuttgart': 4,
    'Mykonos': 2,
    'Helsinki': 5,
    'Split': 3,
    'London': 5,
    'Madrid': 2
}

flight_graph = {
    'Helsinki': ['London', 'Madrid', 'Split', 'Brussels'],
    'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Stuttgart', 'Split', 'Mykonos'],
    'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
    'Madrid': ['Split', 'Helsinki', 'London', 'Brussels', 'Bucharest', 'Mykonos'],
    'Brussels': ['London', 'Bucharest', 'Helsinki', 'Madrid'],
    'Bucharest': ['London', 'Brussels', 'Madrid'],
    'Stuttgart': ['London', 'Split'],
    'Mykonos': ['Madrid', 'London']
}

def is_valid_connection(route):
    for i in range(len(route)-1):
        if route[i+1] not in flight_graph[route[i]]:
            return False
    return True

def validate_itinerary(itinerary):
    days = {}
    for entry in itinerary:
        start = int(entry['day_range'].split()[1].split('-')[0])
        end = int(entry['day_range'].split()[-1])
        city = entry['place']
        days[city] = days.get(city, 0) + (end - start + 1)
    
    for city, req in cities.items():
        if days.get(city, 0) != req:
            return False
    
    madrid_days = [e for e in itinerary if e['place'] == 'Madrid'][0]['day_range']
    if madrid_days != 'Day 20-21':
        return False
    
    stuttgart_days = [e for e in itinerary if e['place'] == 'Stuttgart'][0]['day_range']
    start = int(stuttgart_days.split()[1].split('-')[0])
    if not (1 <= start <= 4):
        return False
    
    return True

target_cities = [c for c in cities if c != 'Madrid']
solution_found = False

for perm in itertools.permutations(target_cities):
    route = list(perm) + ['Madrid']
    if not is_valid_connection(route):
        continue
    
    current_day = 1
    itinerary = []
    valid = True
    for city in route:
        duration = cities[city]
        end_day = current_day + duration - 1
        if city == 'Madrid' and end_day != 21:
            valid = False
            break
        itinerary.append({
            'day_range': f"Day {current_day}-{end_day}" if current_day != end_day else f"Day {current_day}",
            'place': city
        })
        current_day = end_day + 1
    
    if valid and validate_itinerary(itinerary):
        solution_found = True
        print(json.dumps({'itinerary': itinerary}))
        break

if not solution_found:
    print(json.dumps({'itinerary': []}))