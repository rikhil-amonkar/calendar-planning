import itertools
import json

# Define the cities and constraints
cities = ['Mykonos', 'Nice', 'London', 'Copenhagen', 'Oslo', 'Tallinn']
direct_flights = {
    frozenset({'London', 'Copenhagen'}),
    frozenset({'Copenhagen', 'Tallinn'}),
    frozenset({'Tallinn', 'Oslo'}),
    frozenset({'Mykonos', 'London'}),
    frozenset({'Oslo', 'Nice'}),
    frozenset({'London', 'Nice'}),
    frozenset({'Mykonos', 'Nice'}),
    frozenset({'London', 'Oslo'}),
    frozenset({'Copenhagen', 'Nice'}),
    frozenset({'Copenhagen', 'Oslo'}),
}

required_days = {
    'Mykonos': 4,
    'Nice': 3,
    'London': 2,
    'Copenhagen': 3,
    'Oslo': 5,
    'Tallinn': 4
}

valid_itineraries = []

for perm in itertools.permutations(cities):
    if perm[-1] != 'Nice':
        continue  # Nice must be last

    # Check if all consecutive cities have direct flights
    valid_transitions = True
    for i in range(len(perm) - 1):
        city_a, city_b = perm[i], perm[i+1]
        if frozenset({city_a, city_b}) not in direct_flights:
            valid_transitions = False
            break
    if not valid_transitions:
        continue

    # Calculate days for each city in the itinerary
    current_start = 1
    city_days = {}
    for city in perm:
        duration = required_days[city]
        end_day = current_start + duration - 1
        city_days[city] = (current_start, end_day)
        current_start = end_day  # Next city starts on the end day of the previous

    # Check if Nice is correctly placed (days 14-16)
    nice_start, nice_end = city_days.get('Nice', (0, 0))
    if nice_start != 14 or nice_end != 16:
        continue

    # Check if Oslo's stay includes days between 10-14
    oslo_start, oslo_end = city_days.get('Oslo', (0, 0))
    if oslo_start == 0:  # Oslo is not in the itinerary
        continue
    if not (oslo_start <= 14 and oslo_end >= 10):
        continue

    # Check all required days are met
    all_days_correct = True
    for city in perm:
        start, end = city_days[city]
        if end - start + 1 != required_days[city]:
            all_days_correct = False
            break
    if not all_days_correct:
        continue

    # If we reach here, the itinerary is valid
    valid_itineraries.append(perm)
    # Break after first valid itinerary found
    break

# Generate the JSON output
if valid_itineraries:
    itinerary = valid_itineraries[0]
    # Recompute city_days for this itinerary
    current_start = 1
    city_days = {}
    for city in itinerary:
        duration = required_days[city]
        end_day = current_start + duration - 1
        city_days[city] = (current_start, end_day)
        current_start = end_day

    result = {"itinerary": []}
    for city in itinerary:
        start, end = city_days[city]
        day_range = f"Day {start}-{end}"
        result["itinerary"].append({"day_range": day_range, "place": city})
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}))