import json
from itertools import permutations

cities = ['Dublin', 'Riga', 'Vilnius']
durations = {
    'Dublin': 2,
    'Riga': 5,
    'Vilnius': 7
}
allowed_flights = {('Dublin', 'Riga'), ('Riga', 'Dublin'), ('Riga', 'Vilnius'), ('Vilnius', 'Riga')}

valid_order = None
for order in permutations(cities):
    valid = True
    for i in range(1, len(order)):
        if (order[i-1], order[i]) not in allowed_flights:
            valid = False
            break
    if valid:
        valid_order = order
        break

itinerary = []
previous_end = 0
for i, city in enumerate(valid_order):
    if i == 0:
        start_day = 1
    else:
        start_day = previous_end
    duration = durations[city]
    end_day = start_day + duration - 1
    day_range = f"Day {start_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    previous_end = end_day

result = {"itinerary": itinerary}
print(json.dumps(result))