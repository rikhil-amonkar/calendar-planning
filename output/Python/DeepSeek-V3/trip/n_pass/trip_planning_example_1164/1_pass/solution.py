import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Reykjavik': {'days': 2, 'constraints': [(3, 4)]},
        'Stockholm': {'days': 2, 'constraints': [(4, 5)]},
        'Porto': {'days': 5, 'constraints': [(13, 17)]},
        'Nice': {'days': 3, 'constraints': []},
        'Venice': {'days': 4, 'constraints': []},
        'Vienna': {'days': 3, 'constraints': [(11, 13)]},
        'Split': {'days': 3, 'constraints': []},
        'Copenhagen': {'days': 2, 'constraints': []}
    }

    flight_routes = {
        'Copenhagen': ['Vienna', 'Split', 'Nice', 'Stockholm', 'Porto', 'Venice', 'Reykjavik'],
        'Nice': ['Stockholm', 'Reykjavik', 'Porto', 'Venice', 'Vienna', 'Copenhagen'],
        'Split': ['Copenhagen', 'Stockholm', 'Vienna'],
        'Reykjavik': ['Nice', 'Vienna', 'Copenhagen', 'Stockholm'],
        'Stockholm': ['Nice', 'Copenhagen', 'Split', 'Vienna', 'Reykjavik'],
        'Porto': ['Nice', 'Copenhagen', 'Vienna'],
        'Venice': ['Nice', 'Vienna', 'Copenhagen'],
        'Vienna': ['Copenhagen', 'Nice', 'Reykjavik', 'Stockholm', 'Venice', 'Split', 'Porto']
    }

    city_list = list(cities.keys())
    total_days = 17

    for perm in permutations(city_list):
        itinerary = []
        current_day = 1
        valid = True

        for i, city in enumerate(perm):
            if i > 0:
                prev_city = perm[i-1]
                if city not in flight_routes[prev_city]:
                    valid = False
                    break

            days_needed = cities[city]['days']
            constraints = cities[city]['constraints']

            if constraints:
                for (start, end) in constraints:
                    if not (current_day <= start and current_day + days_needed - 1 >= end):
                        valid = False
                        break
                    if not valid:
                        break

            itinerary.append((current_day, current_day + days_needed - 1, city))
            current_day += days_needed

            if current_day - 1 > total_days:
                valid = False
                break

        if valid and current_day - 1 == total_days:
            result = []
            for (start, end, city) in itinerary:
                if start == end:
                    day_str = f"Day {start}"
                else:
                    day_str = f"Day {start}-{end}"
                result.append({"day_range": day_str, "place": city})
            return {"itinerary": result}

    return {"itinerary": []}

if __name__ == "__main__":
    itinerary = find_itinerary()
    print(json.dumps(itinerary))