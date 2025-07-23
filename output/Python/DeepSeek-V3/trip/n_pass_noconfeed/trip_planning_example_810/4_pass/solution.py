import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Berlin': {'days': 3, 'constraints': [(1, 'conference'), (3, 'conference')]},
        'Nice': {'days': 5, 'constraints': []},
        'Athens': {'days': 5, 'constraints': []},
        'Stockholm': {'days': 5, 'constraints': []},
        'Barcelona': {'days': 2, 'constraints': [(3, 'workshop'), (4, 'workshop')]},
        'Vilnius': {'days': 4, 'constraints': []},
        'Lyon': {'days': 2, 'constraints': [(4, 'wedding'), (5, 'wedding')]}
    }

    direct_flights = {
        'Lyon': ['Nice', 'Barcelona'],
        'Nice': ['Lyon', 'Athens', 'Berlin', 'Barcelona', 'Stockholm'],
        'Athens': ['Nice', 'Berlin', 'Stockholm', 'Vilnius', 'Barcelona'],
        'Stockholm': ['Athens', 'Berlin', 'Nice', 'Barcelona'],
        'Berlin': ['Nice', 'Athens', 'Barcelona', 'Vilnius', 'Stockholm'],
        'Barcelona': ['Berlin', 'Nice', 'Athens', 'Stockholm', 'Lyon'],
        'Vilnius': ['Berlin', 'Athens']
    }

    city_names = list(cities.keys())
    for perm in permutations(city_names):
        # Berlin must be first due to day 1 conference
        if perm[0] != 'Berlin':
            continue
            
        # Check flight connections
        valid_flights = True
        for i in range(len(perm)-1):
            if perm[i+1] not in direct_flights[perm[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue

        # Assign days and check constraints
        day_assignments = {}
        current_day = 1
        for city in perm:
            days_needed = cities[city]['days']
            day_assignments[city] = (current_day, current_day + days_needed - 1)
            current_day += days_needed

        # Total trip must be exactly 20 days
        if current_day - 1 != 20:
            continue

        # Check Berlin constraints (must cover days 1 and 3)
        berlin_start, berlin_end = day_assignments['Berlin']
        if not (berlin_start <= 1 <= berlin_end and berlin_start <= 3 <= berlin_end):
            continue

        # Check Barcelona constraints (must cover day 3 or 4)
        if 'Barcelona' in day_assignments:
            barcelona_start, barcelona_end = day_assignments['Barcelona']
            barcelona_constraints_met = any(
                barcelona_start <= day <= barcelona_end 
                for day, _ in cities['Barcelona']['constraints']
            )
            if not barcelona_constraints_met:
                continue

        # Check Lyon constraints (must cover day 4 or 5)
        if 'Lyon' in day_assignments:
            lyon_start, lyon_end = day_assignments['Lyon']
            lyon_constraints_met = any(
                lyon_start <= day <= lyon_end
                for day, _ in cities['Lyon']['constraints']
            )
            if not lyon_constraints_met:
                continue

        # If we got here, all constraints are satisfied
        itinerary = []
        for city in perm:
            start, end = day_assignments[city]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})

        return {"itinerary": itinerary}

    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))