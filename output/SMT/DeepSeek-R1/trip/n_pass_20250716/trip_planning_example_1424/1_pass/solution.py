import itertools

cities_list = ['Warsaw', 'Porto', 'Naples', 'Brussels', 'Split', 'Reykjavik', 'Amsterdam', 'Lyon', 'Helsinki', 'Valencia']
durations = {
    'Warsaw': 3,
    'Porto': 5,
    'Naples': 4,
    'Brussels': 3,
    'Split': 3,
    'Reykjavik': 5,
    'Amsterdam': 4,
    'Lyon': 3,
    'Helsinki': 4,
    'Valencia': 2
}

direct_flights_list = [
    "Amsterdam and Warsaw", "Helsinki and Brussels", "Helsinki and Warsaw", "Reykjavik and Brussels",
    "Amsterdam and Lyon", "Amsterdam and Naples", "Amsterdam and Reykjavik", "Naples and Valencia",
    "Porto and Brussels", "Amsterdam and Split", "Lyon and Split", "Warsaw and Split", "Porto and Amsterdam",
    "Helsinki and Split", "Brussels and Lyon", "Porto and Lyon", "Reykjavik and Warsaw", "Brussels and Valencia",
    "Valencia and Lyon", "Porto and Warsaw", "Warsaw and Valencia", "Amsterdam and Helsinki", "Porto and Valencia",
    "Warsaw and Brussels", "Warsaw and Naples", "Naples and Split", "Helsinki and Naples", "Helsinki and Reykjavik",
    "Amsterdam and Valencia", "Naples and Brussels"
]

flight_set = set()
for flight in direct_flights_list:
    a, b = flight.split(' and ')
    flight_set.add((a, b))
    flight_set.add((b, a))

non_fixed = ['Warsaw', 'Porto', 'Split', 'Reykjavik', 'Amsterdam', 'Lyon', 'Helsinki', 'Valencia']
part1_required = ['Porto', 'Reykjavik', 'Amsterdam', 'Helsinki']
part1_optional = ['Warsaw', 'Split', 'Lyon']

found_solution = False
solution_seq = None
solution_start_days = None

for X in part1_optional:
    part1_cities = part1_required + [X]
    part3_cities = [c for c in non_fixed if c not in part1_cities]
    
    for p1 in itertools.permutations(part1_cities):
        for p3 in itertools.permutations(part3_cities):
            seq = list(p1) + ['Naples', 'Brussels'] + list(p3)
            start_days = [0] * 10
            start_days[0] = 1
            for i in range(1, 10):
                start_days[i] = start_days[i-1] + durations[seq[i-1]] - 1
            
            valid_events = True
            for i in range(5):
                city = seq[i]
                s = start_days[i]
                if city == 'Porto':
                    if not (1 <= s <= 5):
                        valid_events = False
                        break
                elif city == 'Amsterdam':
                    if not (2 <= s <= 8):
                        valid_events = False
                        break
                elif city == 'Helsinki':
                    if not (5 <= s <= 11):
                        valid_events = False
                        break
            if not valid_events:
                continue
            
            valid_flights = True
            for i in range(9):
                c1 = seq[i]
                c2 = seq[i+1]
                if (c1, c2) not in flight_set:
                    valid_flights = False
                    break
            if not valid_flights:
                continue
            
            if start_days[9] + durations[seq[9]] - 1 == 27:
                found_solution = True
                solution_seq = seq
                solution_start_days = start_days
                break
        if found_solution:
            break
    if found_solution:
        break

if not found_solution:
    print("No solution found")
    exit()

end_days = [0] * 10
for i in range(10):
    end_days[i] = solution_start_days[i] + durations[solution_seq[i]] - 1

itinerary = []
for i in range(9):
    s = solution_start_days[i]
    e = end_days[i]
    city = solution_seq[i]
    itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
    itinerary.append({"day_range": f"Day {e}", "place": city})
    next_city = solution_seq[i+1]
    itinerary.append({"day_range": f"Day {e}", "place": next_city})

last_city = solution_seq[9]
s_last = solution_start_days[9]
e_last = end_days[9]
itinerary.append({"day_range": f"Day {s_last}-{e_last}", "place": last_city})

output = {"itinerary": itinerary}
print(output)