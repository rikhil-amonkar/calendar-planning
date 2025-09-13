from z3 import *
import json

# Define the cities and their durations
Cities, (Paris, Florence, Vienna, Porto, Munich, Nice, Warsaw) = EnumSort('Cities', ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw'])

order = [Const(f'city_{i}', Cities) for i in range(7)]

s = Solver()

# All cities are distinct
s.add(Distinct(order))

# First city is Porto
s.add(order[0] == Porto)

# Durations for each city (using Enum elements)
durations = {
    Paris: 5,
    Florence: 3,
    Vienna: 2,
    Porto: 3,
    Munich: 5,
    Nice: 5,
    Warsaw: 3
}

# Durations for each city (using string keys)
durations_str = {
    'Paris': 5,
    'Florence': 3,
    'Vienna': 2,
    'Porto': 3,
    'Munich': 5,
    'Nice': 5,
    'Warsaw': 3
}

# Cumulative durations
cum_dur = [Int(f'cum_dur_{i}') for i in range(7)]
s.add(cum_dur[0] == 0)

for i in range(1, 7):
    prev_city = order[i-1]
    # Build the duration expression for prev_city
    dur_expr = If(prev_city == Paris, 5,
        If(prev_city == Florence, 3,
            If(prev_city == Vienna, 2,
                If(prev_city == Porto, 3,
                    If(prev_city == Munich, 5,
                        If(prev_city == Nice, 5, 3)  # Warsaw's duration
                    )
                )
            )
        )
    )
    s.add(cum_dur[i] == cum_dur[i-1] + dur_expr)

# Compute start_days for each position
start_days = [Int(f'start_day_{i}') for i in range(7)]
for i in range(7):
    s.add(start_days[i] == 1 + cum_dur[i] - i)

# Constraints for Warsaw and Vienna
war_pos = []
for i in range(7):
    war_pos.append(And(order[i] == Warsaw, start_days[i] == 13))
s.add(Or(*war_pos))

vie_pos = []
for j in range(7):
    vie_pos.append(And(order[j] == Vienna, start_days[j] == 19))
s.add(Or(*vie_pos))

# Allowed pairs for direct flights (using Enum elements)
allowed_pairs = {
    (Paris, Warsaw), (Warsaw, Paris),
    (Munich, Vienna), (Vienna, Munich),
    (Porto, Vienna), (Vienna, Porto),
    (Warsaw, Vienna), (Vienna, Warsaw),
    (Florence, Munich),  # one-way
    (Munich, Warsaw), (Warsaw, Munich),
    (Munich, Nice), (Nice, Munich),
    (Paris, Florence), (Florence, Paris),
    (Warsaw, Nice), (Nice, Warsaw),
    (Porto, Munich), (Munich, Porto),
    (Porto, Nice), (Nice, Porto),
    (Paris, Vienna), (Vienna, Paris),
    (Nice, Vienna), (Vienna, Nice),
    (Porto, Paris), (Paris, Porto),
    (Paris, Nice), (Nice, Paris),
    (Paris, Munich), (Munich, Paris),
    (Porto, Warsaw), (Warsaw, Porto),
    (Florence, Vienna), (Vienna, Florence)
}

# Add constraints for consecutive flights
for i in range(6):
    current = order[i]
    next_city = order[i+1]
    constraints = []
    for (a, b) in allowed_pairs:
        constraints.append(And(current == a, next_city == b))
    s.add(Or(*constraints))

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    # Extract the order as strings
    order_result = [model[order[i]].as_string() for i in range(7)]
    # Compute start and end days for each city
    itinerary = []
    for i in range(7):
        city_name = order_result[i]
        start_day = model[start_days[i]].as_long()
        end_day = start_day + durations_str[city_name] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_name
        })
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")