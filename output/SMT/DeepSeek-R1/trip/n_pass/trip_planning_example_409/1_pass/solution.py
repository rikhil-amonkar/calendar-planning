from z3 import *
import json

# Mapping cities to integers
cities = ["Zurich", "Helsinki", "Hamburg", "Bucharest", "Split"]
city_to_int = {city: idx for idx, city in enumerate(cities)}
int_to_city = {idx: city for idx, city in enumerate(cities)}

allowed_pairs = [
    (0, 1), (1, 0),
    (2, 3), (3, 2),
    (1, 2), (2, 1),
    (0, 2), (2, 0),
    (0, 3), (3, 0),
    (0, 4), (4, 0),
    (1, 4), (4, 1),
    (4, 2), (2, 4)
]

s = [Int(f's_{i}') for i in range(12)]
e = [Int(f'e_{i}') for i in range(12)]

solver = Solver()

for i in range(12):
    solver.add(And(s[i] >= 0, s[i] <= 4))
    solver.add(And(e[i] >= 0, e[i] <= 4))

for i in range(11):
    solver.add(e[i] == s[i+1])

for i in range(12):
    flight_condition = Or([And(s[i] == a, e[i] == b) for (a, b) in allowed_pairs])
    solver.add(If(s[i] != e[i], flight_condition, BoolVal(True)))

counts = [0] * 5
for city in range(5):
    total = 0
    for i in range(12):
        total = total + If(s[i] == city, 1, 0)
        total = total + If(And(s[i] != e[i], e[i] == city), 1, 0)
    counts[city] = total

solver.add(counts[city_to_int["Zurich"]] == 3)
solver.add(counts[city_to_int["Helsinki"]] == 2)
solver.add(counts[city_to_int["Hamburg"]] == 2)
solver.add(counts[city_to_int["Bucharest"]] == 2)
solver.add(counts[city_to_int["Split"]] == 7)

wedding_constraint = Or(
    Or(s[0] == city_to_int["Zurich"], And(s[0] != e[0], e[0] == city_to_int["Zurich"])),
    Or(s[1] == city_to_int["Zurich"], And(s[1] != e[1], e[1] == city_to_int["Zurich"])),
    Or(s[2] == city_to_int["Zurich"], And(s[2] != e[2], e[2] == city_to_int["Zurich"]))
)
solver.add(wedding_constraint)

solver.add(Or(s[3] == city_to_int["Split"], e[3] == city_to_int["Split"]))
solver.add(Or(s[9] == city_to_int["Split"], e[9] == city_to_int["Split"]))

if solver.check() == sat:
    model = solver.model()
    s_val = [model.evaluate(s_i).as_long() for s_i in s]
    e_val = [model.evaluate(e_i).as_long() for e_i in e]
    
    days_in_city = {i: set() for i in range(5)}
    for i in range(12):
        day = i+1
        start_city = s_val[i]
        days_in_city[start_city].add(day)
        if s_val[i] != e_val[i]:
            end_city = e_val[i]
            days_in_city[end_city].add(day)
    
    itinerary_blocks = []
    for city in range(5):
        if days_in_city[city]:
            sorted_days = sorted(days_in_city[city])
            start_block = sorted_days[0]
            end_block = start_block
            blocks = []
            for idx in range(1, len(sorted_days)):
                if sorted_days[idx] == end_block + 1:
                    end_block = sorted_days[idx]
                else:
                    blocks.append((start_block, end_block))
                    start_block = sorted_days[idx]
                    end_block = start_block
            blocks.append((start_block, end_block))
            for (start, end) in blocks:
                if start == end:
                    day_str = f"Day {start}"
                else:
                    day_str = f"Day {start}-{end}"
                itinerary_blocks.append((start, day_str, city))
    
    itinerary_flights = []
    for i in range(12):
        if s_val[i] != e_val[i]:
            day = i+1
            day_str = f"Day {day}"
            itinerary_flights.append((day, day_str, s_val[i]))
            itinerary_flights.append((day, day_str, e_val[i]))
    
    events = []
    for (start, day_str, city) in itinerary_blocks:
        events.append((start, 1, day_str, int_to_city[city]))
    for (day, day_str, city) in itinerary_flights:
        events.append((day, 0, day_str, int_to_city[city]))
    
    events_sorted = sorted(events, key=lambda x: (x[0], x[1]))
    itinerary_list = [{"day_range": day_str, "place": city_name} for (_, _, day_str, city_name) in events_sorted]
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")