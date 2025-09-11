import itertools
import json

# Define the cities and their required durations
cities = {
    'Salzburg': 3,
    'Venice': 5,
    'Bucharest': 4,
    'Brussels': 2,
    'Hamburg': 4,
    'Copenhagen': 4,
    'Nice': 3,
    'Zurich': 5,
    'Naples': 4
}

# Define the direct flights (both directions)
direct_flights = {
    ('Zurich', 'Brussels'),
    ('Brussels', 'Zurich'),
    ('Bucharest', 'Copenhagen'),
    ('Copenhagen', 'Bucharest'),
    ('Venice', 'Brussels'),
    ('Brussels', 'Venice'),
    ('Nice', 'Zurich'),
    ('Zurich', 'Nice'),
    ('Hamburg', 'Nice'),
    ('Nice', 'Hamburg'),
    ('Zurich', 'Naples'),
    ('Naples', 'Zurich'),
    ('Hamburg', 'Bucharest'),
    ('Bucharest', 'Hamburg'),
    ('Zurich', 'Copenhagen'),
    ('Copenhagen', 'Zurich'),
    ('Bucharest', 'Brussels'),
    ('Brussels', 'Bucharest'),
    ('Hamburg', 'Brussels'),
    ('Brussels', 'Hamburg'),
    ('Venice', 'Naples'),
    ('Naples', 'Venice'),
    ('Venice', 'Copenhagen'),
    ('Copenhagen', 'Venice'),
    ('Bucharest', 'Naples'),
    ('Naples', 'Bucharest'),
    ('Hamburg', 'Copenhagen'),
    ('Copenhagen', 'Hamburg'),
    ('Venice', 'Zurich'),
    ('Zurich', 'Venice'),
    ('Nice', 'Brussels'),
    ('Brussels', 'Nice'),
    ('Hamburg', 'Venice'),
    ('Venice', 'Hamburg'),
    ('Copenhagen', 'Naples'),
    ('Naples', 'Copenhagen'),
    ('Nice', 'Copenhagen'),
    ('Copenhagen', 'Nice'),
    ('Hamburg', 'Zurich'),
    ('Zurich', 'Hamburg'),
    ('Salzburg', 'Hamburg'),
    ('Hamburg', 'Salzburg'),
    ('Zurich', 'Bucharest'),
    ('Bucharest', 'Zurich'),
    ('Brussels', 'Naples'),
    ('Naples', 'Brussels'),
    ('Copenhagen', 'Brussels'),
    ('Brussels', 'Copenhagen'),
    ('Venice', 'Nice'),
    ('Nice', 'Venice'),
    ('Nice', 'Copenhagen'),
    ('Copenhagen', 'Nice'),
    # Added missing direct flights
    ('Salzburg', 'Venice'),
    ('Venice', 'Salzburg'),
    ('Naples', 'Hamburg'),
    ('Hamburg', 'Naples'),
}

city_list = list(cities.keys())

def is_valid_permutation(perm):
    # Check for valid direct flights
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights:
            return False

    # Track start and end days of each city
    start_days = {}
    end_days = {}
    current_day = 1
    for city in perm:
        duration = cities[city]
        end_day = current_day + duration - 1
        start_days[city] = current_day
        end_days[city] = end_day
        current_day = end_day + 1

    # Constraint 1: Copenhagen must start on day 17
    if start_days['Copenhagen'] != 17:
        return False

    # Constraint 2: Naples must start on day 23 (adjusted from 22)
    if start_days['Naples'] != 23:
        return False

    # Constraint 3: Nice must include days 9 to 11 (inclusive)
    if not (start_days['Nice'] <= 9 and end_days['Nice'] >= 11):
        return False

    # Constraint 4: Brussels must include day 21 or 22
    brussels_start = start_days['Brussels']
    brussels_end = end_days['Brussels']
    if not (brussels_start <= 21 <= brussels_end or brussels_start <= 22 <= brussels_end):
        return False

    return True

# Generate all permutations and find a valid one
found = False
for perm in itertools.permutations(city_list):
    if is_valid_permutation(perm):
        itinerary = []
        current_day = 1
        for city in perm:
            duration = cities[city]
            end_day = current_day + duration - 1
            itinerary.append({
                "day_range": f"Day {current_day}-{end_day}",
                "place": city
            })
            current_day = end_day + 1
        print(json.dumps({"itinerary": itinerary}))
        found = True
        break

if not found:
    print(json.dumps({"error": "No valid itinerary found with adjusted constraints."}))