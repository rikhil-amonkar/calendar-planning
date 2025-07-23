from z3 import *

# Initialize the solver
s = Solver()

# Define the districts
districts = ['Richmond', 'Sunset', 'Haight', 'Mission', 'GoldenGate']
n = len(districts)

# Travel times matrix (minutes)
travel_times = {
    ('Richmond', 'Sunset'): 11,
    ('Richmond', 'Haight'): 10,
    ('Richmond', 'Mission'): 20,
    ('Richmond', 'GoldenGate'): 9,
    ('Sunset', 'Richmond'): 12,
    ('Sunset', 'Haight'): 15,
    ('Sunset', 'Mission'): 24,
    ('Sunset', 'GoldenGate'): 11,
    ('Haight', 'Richmond'): 10,
    ('Haight', 'Sunset'): 15,
    ('Haight', 'Mission'): 11,
    ('Haight', 'GoldenGate'): 7,
    ('Mission', 'Richmond'): 20,
    ('Mission', 'Sunset'): 24,
    ('Mission', 'Haight'): 12,
    ('Mission', 'GoldenGate'): 17,
    ('GoldenGate', 'Richmond'): 7,
    ('GoldenGate', 'Sunset'): 10,
    ('GoldenGate', 'Haight'): 7,
    ('GoldenGate', 'Mission'): 17,
}

# Friend constraints
friends = {
    'Sarah': {'district': 'Sunset', 'start': 10.75, 'end': 19.0, 'duration': 0.5},
    'Richard': {'district': 'Haight', 'start': 11.75, 'end': 15.75, 'duration': 1.5},
    'Elizabeth': {'district': 'Mission', 'start': 11.0, 'end': 17.25, 'duration': 2.0},
    'Michelle': {'district': 'GoldenGate', 'start': 18.25, 'end': 20.75, 'duration': 1.5}
}

# Variables for arrival and departure times at each district
arrival = {d: Real(f'arrival_{d}') for d in districts}
departure = {d: Real(f'departure_{d}') for d in districts}

# Initial constraints: start at Richmond at 9:00 AM (9.0)
s.add(arrival['Richmond'] == 9.0)

# Constraints for each friend: must be in their district for the required duration within their availability
for name, info in friends.items():
    district = info['district']
    start = info['start']
    end = info['end']
    duration = info['duration']
    s.add(arrival[district] >= start)
    s.add(departure[district] <= end)
    s.add(departure[district] >= arrival[district] + duration)

# Travel time constraints: if you go from A to B, departure_A + travel_time <= arrival_B
# We need to model the sequence of visits. For simplicity, assume a linear sequence.
# This is a simplification; a more accurate model would allow for any order.
# For now, we'll assume the order is Richmond -> Sunset -> Haight -> Mission -> GoldenGate
# This may not be optimal, but it's a starting point.
order = ['Richmond', 'Sunset', 'Haight', 'Mission', 'GoldenGate']
for i in range(len(order) - 1):
    from_district = order[i]
    to_district = order[i + 1]
    s.add(departure[from_district] + travel_times[(from_district, to_district)] / 60 <= arrival[to_district])

# Ensure all times are positive
for d in districts:
    s.add(arrival[d] >= 0)
    s.add(departure[d] >= 0)

# Objective: maximize the number of friends met (all in this case, but could be adjusted)
# Alternatively, minimize total time spent traveling or maximize free time.
# Here, we'll just check feasibility.

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    for d in districts:
        print(f"{d}: Arrival = {m[arrival[d]]}, Departure = {m[departure[d]]}")
else:
    print("No feasible schedule found.")