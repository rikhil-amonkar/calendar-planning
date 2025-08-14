import itertools
import json

# Define cities and their required durations
cities = ['Riga', 'Brussels', 'Geneva', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest']
durations = {
    'Riga': 4,
    'Brussels': 5,
    'Geneva': 5,
    'Rome': 2,
    'Dubrovnik': 3,
    'Valencia': 2,
    'Budapest': 2,
}

# Define direct flight connections (bidirectional)
direct_flights = {
    'Brussels': ['Valencia', 'Geneva', 'Rome', 'Budapest', 'Riga'],
    'Rome': ['Valencia', 'Geneva', 'Dubrovnik', 'Budapest', 'Brussels', 'Riga'],
    'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
    'Dubrovnik': ['Geneva', 'Rome'],
    'Valencia': ['Brussels', 'Rome', 'Geneva'],
    'Budapest': ['Geneva', 'Rome', 'Brussels'],
    'Riga': ['Brussels', 'Rome'],
}

# Generate all permutations of the cities
for perm in itertools.permutations(cities):
    valid = True
    # Check if all consecutive cities have a direct flight
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i + 1]
        if next_city not in direct_flights[current]:
            valid = False
            break
    if not valid:
        continue

    # Calculate start and end days for each city
    start_days = {}
    end_days = {}
    current_start = 1
    for city in perm:
        duration = durations[city]
        start_days[city] = current_start
        end_days[city] = current_start + duration - 1
        current_start = end_days[city]  # Next city starts on the same day as this city's end

    # Check constraints
    # Brussels must include at least one day between day 7 and day 11
    brussels_start = start_days.get('Brussels', 0)
    brussels_end = end_days.get('Brussels', 0)
    brussels_overlap = not (brussels_end < 7 or brussels_start > 11)
    if not brussels_overlap:
        continue

    # Riga must include at least one day between day 4 and day 7
    riga_start = start_days.get('Riga', 0)
    riga_end = end_days.get('Riga', 0)
    riga_overlap = not (riga_end < 4 or riga_start > 7)
    if not riga_overlap:
        continue

    # Budapest must be days 16-17
    budapest_start = start_days.get('Budapest', 0)
    budapest_end = end_days.get('Budapest', 0)
    if not (budapest_start == 16 and budapest_end == 17):
        continue

    # Construct the itinerary
    itinerary = []
    current_start = 1
    for city in perm:
        duration = durations[city]
        end = current_start + duration - 1
        day_range = f"Day {current_start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
        current_start = end  # Next city starts on the same day as this city's end

    # Output the result
    print(json.dumps({"itinerary": itinerary}, indent=2))
    exit()