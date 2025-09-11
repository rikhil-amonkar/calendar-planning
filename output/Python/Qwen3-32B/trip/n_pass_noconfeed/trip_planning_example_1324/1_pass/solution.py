import itertools
import json

cities = {
    'Venice': {'duration': 4},
    'Barcelona': {'duration': 3, 'start_range': (10, 12)},
    'Copenhagen': {'duration': 4, 'start_range': (7, 10)},
    'Lyon': {'duration': 4},
    'Reykjavik': {'duration': 4},
    'Dubrovnik': {'duration': 5, 'start_range': (16, 20)},
    'Athens': {'duration': 2},
    'Tallinn': {'duration': 5},
    'Munich': {'duration': 3},
}

direct_flights = {
    'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Barcelona', 'Venice', 'Reykjavik', 'Tallinn'],
    'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Munich', 'Barcelona', 'Reykjavik'],
    'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Lyon', 'Dubrovnik', 'Barcelona', 'Athens'],
    'Venice': ['Munich', 'Copenhagen', 'Athens', 'Lyon', 'Barcelona'],
    'Lyon': ['Barcelona', 'Munich', 'Venice'],
    'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
    'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
    'Barcelona': ['Lyon', 'Venice', 'Copenhagen', 'Munich', 'Tallinn', 'Athens', 'Dubrovnik', 'Reykjavik'],
    'Tallinn': ['Munich', 'Barcelona', 'Copenhagen'],
}

city_list = list(cities.keys())

def is_valid_permutation(perm):
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i+1]
        if next_city not in direct_flights[current]:
            return False
    return True

def calculate_start_days(perm):
    start_days = [1]
    for i in range(len(perm) - 1):
        start_days.append(start_days[-1] + cities[perm[i]]['duration'])
    return start_days

def check_constraints(perm, start_days):
    for i, city in enumerate(perm):
        if 'start_range' in cities[city]:
            start, end = cities[city]['start_range']
            if not (start <= start_days[i] <= end):
                return False
    return True

for perm in itertools.permutations(city_list):
    if not is_valid_permutation(perm):
        continue
    start_days = calculate_start_days(perm)
    if not check_constraints(perm, start_days):
        continue
    total_days = start_days[-1] + cities[perm[-1]]['duration'] - 1
    if total_days != 26:
        continue
    itinerary = []
    for i in range(len(perm)):
        start = start_days[i]
        duration = cities[perm[i]]['duration']
        end = start + duration - 1
        day_range = f"Day {start}-Day {end}"
        itinerary.append({"day_range": day_range, "place": perm[i]})
    print(json.dumps({"itinerary": itinerary}))
    exit()

print(json.dumps({"itinerary": []}))