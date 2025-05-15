import z3

# Define cities with their durations and fixed dates where applicable
cities = {
    'Barcelona': (2, (5, 6)),
    'Venice': (5, (6, 10)),
    'Naples': (3, (18, 20)),
    'Nice': (2, (23, 24)),
    'Valencia': 5,
    'Stuttgart': 2,
    'Split': 5,
    'Amsterdam': 4,
    'Porto': 4,
}

# Define flight connections as a set of tuples
flight_pairs = {
    ('Venice', 'Nice'),
    ('Naples', 'Amsterdam'),
    ('Barcelona', 'Nice'),
    ('Amsterdam', 'Nice'),
    ('Stuttgart', 'Valencia'),
    ('Stuttgart', 'Porto'),
    ('Split', 'Stuttgart'),
    ('Split', 'Naples'),
    ('Valencia', 'Amsterdam'),
    ('Barcelona', 'Porto'),
    ('Valencia', 'Naples'),
    ('Venice', 'Amsterdam'),
    ('Barcelona', 'Naples'),
    ('Barcelona', 'Valencia'),
    ('Split', 'Amsterdam'),
    ('Barcelona', 'Venice'),
    ('Stuttgart', 'Amsterdam'),
    ('Naples', 'Nice'),
    ('Venice', 'Stuttgart'),
    ('Split', 'Barcelona'),
    ('Porto', 'Nice'),
    ('Barcelona', 'Stuttgart'),
    ('Venice', 'Naples'),
    ('Porto', 'Amsterdam'),
    ('Porto', 'Valencia'),
    ('Stuttgart', 'Naples'),
    ('Barcelona', 'Amsterdam'),
}

# Helper function to check if two cities are connected
def is_connected(a, b):
    return (a, b) in flight_pairs or (b, a) in flight_pairs

# Initialize solver
solver = z3.Solver()

# Create variables for non-fixed cities
non_fixed = {
    'Valencia': (z3.Int('valencia_start'), z3.Int('valencia_end')),
    'Stuttgart': (z3.Int('stuttgart_start'), z3.Int('stuttgart_end')),
    'Split': (z3.Int('split_start'), z3.Int('split_end')),
    'Amsterdam': (z3.Int('amsterdam_start'), z3.Int('amsterdam_end')),
    'Porto': (z3.Int('porto_start'), z3.Int('porto_end')),
}

# Duration constraints for non-fixed cities
for city, (start, end) in non_fixed.items():
    duration = cities[city]
    solver.add(end == start + duration - 1)
    solver.add(start >= 1, end <= 24)

# Collect all city intervals
all_intervals = []
for city in cities:
    if city in ['Barcelona', 'Venice', 'Naples', 'Nice']:
        dur, (s, e) = cities[city]
        all_intervals.append((city, s, e))
    else:
        s, e = non_fixed[city]
        all_intervals.append((city, s, e))

# Ensure each consecutive city in the sequence is connected and contiguous
for i in range(len(all_intervals)):
    for j in range(len(all_intervals)):
        if i == j:
            continue
        # i comes before j
        before = all_intervals[i]
        after = all_intervals[j]
        # If before ends when after starts, they must be connected
        conn = z3.And(
            before[2] == after[1],
            z3.BoolVal(is_connected(before[0], after[0]))
        )
        # If before ends before after starts, no overlap
        no_overlap = before[2] < after[1]
        solver.add(z3.Or(conn, no_overlap))

# Fixed city constraints
solver.add(all_intervals[0][1] == 5, all_intervals[0][2] == 6)  # Barcelona
solver.add(all_intervals[1][1] == 6, all_intervals[1][2] == 10)  # Venice
solver.add(all_intervals[2][1] == 18, all_intervals[2][2] == 20) # Naples
solver.add(all_intervals[3][1] == 23, all_intervals[3][2] == 24) # Nice

# Total days must start at 1 and end at 24
starts = [interval[1] for interval in all_intervals]
ends = [interval[2] for interval in all_intervals]
solver.add(z3.Or([s == 1 for s in starts]))
solver.add(z3.Or([e == 24 for e in ends]))

# Check solution
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for city, start, end in all_intervals:
        if city in ['Barcelona', 'Venice', 'Naples', 'Nice']:
            s = start
            e = end
        else:
            s = model[start].as_long()
            e = model[end].as_long()
        schedule.append((city, s, e))
    # Sort by start day
    schedule.sort(key=lambda x: x[1])
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")