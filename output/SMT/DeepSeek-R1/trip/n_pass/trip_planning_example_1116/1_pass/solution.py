from z3 import *
import json

# Mapping of cities to integers
city_map = {
    "Oslo": 0,
    "Reykjavik": 1,
    "Stockholm": 2,
    "Munich": 3,  # Note: the direct flights list uses "Munich"
    "Frankfurt": 4,
    "Barcelona": 5,
    "Bucharest": 6,
    "Split": 7
}

rev_map = {
    0: "Oslo",
    1: "Reykjavik",
    2: "Stockholm",
    3: "Munich",
    4: "Frankfurt",
    5: "Barcelona",
    6: "Bucharest",
    7: "Split"
}

# Direct flight connections
flights_str = """
Reykjavik and Munich,
Munich and Frankfurt,
Split and Oslo,
Reykjavik and Oslo,
Bucharest and Munich,
Oslo and Frankfurt,
Bucharest and Barcelona,
Barcelona and Frankfurt,
Reykjavik and Frankfurt,
Barcelona and Stockholm,
Barcelona and Reykjavik,
Stockholm and Reykjavik,
Barcelona and Split,
Bucharest and Oslo,
Bucharest and Frankfurt,
Split and Stockholm,
Barcelona and Oslo,
Stockholm and Munich,
Stockholm and Oslo,
Split and Frankfurt,
Barcelona and Munich,
Stockholm and Frankfurt,
Munich and Oslo,
Split and Munich
"""

flight_pairs = []
lines = flights_str.strip().split(',')
for line in lines:
    s_clean = line.strip()
    if not s_clean:
        continue
    parts = s_clean.split(' and ')
    if len(parts) != 2:
        continue
    city1 = parts[0].strip()
    city2 = parts[1].strip()
    if city1 in city_map and city2 in city_map:
        c1 = city_map[city1]
        c2 = city_map[city2]
        flight_pairs.append((c1, c2))
        flight_pairs.append((c2, c1))

# Create Z3 solver
s = Solver()

# 21 base_city variables: base_city[0] to base_city[20]
base_city = [Int(f'base_city_{i}') for i in range(21)]

# Each base_city must be between 0 and 7
for i in range(21):
    s.add(And(base_city[i] >= 0, base_city[i] <= 7))

# Flight constraints for day transitions
for d in range(1, 21):
    prev = base_city[d-1]
    curr = base_city[d]
    # If different, must have a direct flight
    same_city = (prev == curr)
    allowed_flight = Or([And(prev == p0, curr == p1) for (p0, p1) in flight_pairs])
    s.add(If(same_city, True, allowed_flight))

# Total days per city
def total_days(city_idx):
    count = 0
    for d in range(1, 21):  # d: day index from 1 to 20
        # Count base_city[d-1] if it equals city_idx
        count += If(base_city[d-1] == city_idx, 1, 0)
        # Count base_city[d] if it equals city_idx and different from base_city[d-1]
        count += If(And(base_city[d] == city_idx, base_city[d] != base_city[d-1]), 1, 0)
    return count

s.add(total_days(0) == 2)  # Oslo
s.add(total_days(1) == 5)  # Reykjavik
s.add(total_days(2) == 4)  # Stockholm
s.add(total_days(3) == 4)  # Munich
s.add(total_days(4) == 4)  # Frankfurt
s.add(total_days(5) == 3)  # Barcelona
s.add(total_days(6) == 2)  # Bucharest
s.add(total_days(7) == 3)  # Split

# Specific event constraints
# Oslo must be visited on day 16 and 17
s.add(Or(base_city[15] == 0, base_city[16] == 0))  # Day16: base_city[15] and base_city[16] are used for day16
s.add(Or(base_city[16] == 0, base_city[17] == 0))  # Day17

# Reykjavik: at least one day between day9 and day13 (inclusive)
reykjavik_days = []
for d in range(9, 14):  # d: day from 9 to 13
    # For day d, we use base_city[d-1] and base_city[d]
    reykjavik_days.append(Or(base_city[d-1] == 1, base_city[d] == 1))
s.add(Or(reykjavik_days))

# Munich: at least one day between day13 and day16 (inclusive)
munich_days = []
for d in range(13, 17):  # d: day from 13 to 16
    munich_days.append(Or(base_city[d-1] == 3, base_city[d] == 3))
s.add(Or(munich_days))

# Frankfurt: at least one day between day17 and day20 (inclusive)
frankfurt_days = []
for d in range(17, 21):  # d: day from 17 to 20
    frankfurt_days.append(Or(base_city[d-1] == 4, base_city[d] == 4))
s.add(Or(frankfurt_days))

# Check and get model
if s.check() == sat:
    m = s.model()
    base_city_vals = [m[base_city[i]].as_long() for i in range(21)]
    
    # Group consecutive base_city values (for indices 0 to 19) into blocks
    blocks = []
    start_index = 0
    current_city = base_city_vals[0]
    for i in range(1, 20):  # i from 1 to 19 (base_city indices 1 to 19)
        if base_city_vals[i] != current_city:
            blocks.append((current_city, start_index, i-1))
            start_index = i
            current_city = base_city_vals[i]
    blocks.append((current_city, start_index, 19))
    
    # Collect all records for the itinerary
    records = []  # each record is (min_day, type_priority, record_dict)
    
    # Add block records
    for (city, start_idx, end_idx) in blocks:
        start_day = start_idx + 1
        end_day = end_idx + 1
        day_range_str = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
        record_dict = {"day_range": day_range_str, "place": rev_map[city]}
        min_day = start_day
        records.append((min_day, 0, record_dict))  # type_priority 0 for block
    
    # Add flight records
    for d in range(1, 21):  # d: day from 1 to 20
        if base_city_vals[d-1] != base_city_vals[d]:
            # Departure city
            dep_city = base_city_vals[d-1]
            record_dict_dep = {"day_range": f"Day {d}", "place": rev_map[dep_city]}
            records.append((d, 1, record_dict_dep))  # type_priority 1 for flight
            # Arrival city
            arr_city = base_city_vals[d]
            record_dict_arr = {"day_range": f"Day {d}", "place": rev_map[arr_city]}
            records.append((d, 1, record_dict_arr))
    
    # Sort records by min_day (the day the record refers to) and then by type_priority (block first, then flight)
    records_sorted = sorted(records, key=lambda x: (x[0], x[1]))
    itinerary_list = [record[2] for record in records_sorted]
    
    # Create the final JSON
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")