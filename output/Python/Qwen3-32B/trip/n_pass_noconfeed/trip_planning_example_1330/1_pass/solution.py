import itertools
import json

# Define the cities and their required durations
cities = {
    'Salzburg': 2,
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
    ('Copenhagen', 'Nice')
}

# List of city names
city_list = list(cities.keys())

# Function to check if a permutation is valid
def is_valid_permutation(perm):
    # Check direct flights
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights:
            return False
    # Calculate start and end days
    start_days = {}
    end_days = {}
    current_start = 1
    for city in perm:
        duration = cities[city]
        end_days[city] = current_start + duration - 1
        start_days[city] = current_start
        current_start = end_days[city] + 1
    # Check constraints
    # 1. Copenhagen must start on day 18
    if start_days.get('Copenhagen', 0) != 18:
        return False
    # 2. Naples must start on day 22
    if start_days.get('Naples', 0) != 22:
        return False
    # 3. Nice must include days 9-11
    nice_start = start_days.get('Nice', 0)
    nice_end = end_days.get('Nice', 0)
    if not (nice_start <= 11 <= nice_end or nice_start <= 10 <= nice_end or nice_start <= 9 <= nice_end):
        return False
    # 4. Brussels must include day 21 or 22
    brussels_start = start_days.get('Brussels', 0)
    brussels_end = end_days.get('Brussels', 0)
    if not (brussels_start <= 21 <= brussels_end or brussels_start <= 22 <= brussels_end):
        return False
    return True

# Generate permutations and find valid one
for perm in itertools.permutations(city_list):
    if is_valid_permutation(perm):
        # Found valid permutation, calculate itinerary
        itinerary = []
        current_start = 1
        for city in perm:
            duration = cities[city]
            end_day = current_start + duration - 1
            day_range = f"Day {current_start}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
            current_start = end_day + 1
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
        break