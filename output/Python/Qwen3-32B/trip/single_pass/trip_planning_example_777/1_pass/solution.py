import itertools
import json

# Define the cities and their required durations
cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
durations = {
    'Dublin': 5,
    'Helsinki': 3,
    'Riga': 3,
    'Reykjavik': 2,
    'Vienna': 2,
    'Tallinn': 5
}

# Define direct flight connections (bidirectional)
original_pairs = [
    ('Helsinki', 'Riga'),
    ('Riga', 'Tallinn'),
    ('Vienna', 'Helsinki'),
    ('Riga', 'Dublin'),
    ('Vienna', 'Riga'),
    ('Reykjavik', 'Vienna'),
    ('Helsinki', 'Dublin'),
    ('Tallinn', 'Dublin'),
    ('Reykjavik', 'Helsinki'),
    ('Reykjavik', 'Dublin'),
    ('Helsinki', 'Tallinn'),
    ('Vienna', 'Dublin'),
]

direct_flights = set()
for a, b in original_pairs:
    direct_flights.add((a, b))
    direct_flights.add((b, a))

# Iterate through all possible permutations of the cities
for perm in itertools.permutations(cities):
    # Check if all consecutive city pairs have direct flights
    valid_flight = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i + 1]) not in direct_flights:
            valid_flight = False
            break
    if not valid_flight:
        continue

    # Calculate start and end days for each city
    start_days = {}
    end_days = {}
    current_day = 1
    for city in perm:
        dur = durations[city]
        start_days[city] = current_day
        end_days[city] = current_day + dur - 1
        current_day = end_days[city]  # Next city starts on the same day as this city's end

    # Check specific constraints
    # Vienna must be visited during days 2-3
    vienna_start = start_days.get('Vienna', -1)
    vienna_end = end_days.get('Vienna', -1)
    if not (vienna_start <= 2 and vienna_end >= 3):
        continue

    # Helsinki must be visited during days 3-5
    helsinki_start = start_days.get('Helsinki', -1)
    helsinki_end = end_days.get('Helsinki', -1)
    if not (helsinki_start == 3 and helsinki_end == 5):
        continue

    # Tallinn must be visited during days 7-11
    tallinn_start = start_days.get('Tallinn', -1)
    tallinn_end = end_days.get('Tallinn', -1)
    if not (tallinn_start == 7 and tallinn_end == 11):
        continue

    # Build the itinerary
    itinerary = []
    for city in perm:
        start = start_days[city]
        end = end_days[city]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    # Output the result as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
    exit()