from z3 import *
import json

# Convert time to minutes since midnight
def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Convert minutes to HH:MM format
def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Friend data
friends = [
    {'name': 'Brian', 'earliest': to_minutes("09:45"), 'latest': to_minutes("21:45"), 'duration': 15},
    {'name': 'Elizabeth', 'earliest': to_minutes("08:45"), 'latest': to_minutes("21:30"), 'duration': 105},
    {'name': 'Laura', 'earliest': to_minutes("14:15"), 'latest': to_minutes("19:30"), 'duration': 75},
    {'name': 'Jason', 'earliest': to_minutes("13:00"), 'latest': to_minutes("20:45"), 'duration': 90},
    {'name': 'Melissa', 'earliest': to_minutes("18:45"), 'latest': to_minutes("20:15"), 'duration': 45}
]

# Travel matrix between friends' locations
travel_matrix = [
    [0, 23, 9, 21, 7],       # Financial District to others
    [26, 0, 22, 7, 24],      # Golden Gate Park
    [9, 22, 0, 20, 10],      # Union Square
    [22, 9, 21, 0, 17],      # Richmond District
    [8, 22, 7, 18, 0]        # North Beach
]

# Z3 solver
solver = Solver()

# Define order variables (0-4 for each friend)
order = [Int(f'order_{i}') for i in range(5)]
solver.add(Distinct(order))
for i in range(5):
    solver.add(And(0 <= order[i], order[i] <= 4))

# Define arrival and departure times
arrival = [Int(f'arrival_{i}') for i in range(5)]
departure = [Int(f'departure_{i}') for i in range(5)]

# First arrival time (from Presidio to first friend)
presidio_to = [23, 12, 22, 7, 18]  # Financial, Golden, Union, Richmond, North
arrival_0 = 540 + If(order[0] == 0, 23,
                     If(order[0] == 1, 12,
                     If(order[0] == 2, 22,
                     If(order[0] == 3, 7,
                     If(order[0] == 4, 18, 0)))))
solver.add(arrival[0] == arrival_0)

# Travel time expressions between friends
for i in range(1, 5):
    prev = order[i-1]
    curr = order[i]
    travel_time_expr = 0
    travel_time_expr = If(prev == 0,
        If(curr == 0, 0,
           If(curr == 1, 23,
              If(curr == 2, 9,
                 If(curr == 3, 21,
                    If(curr == 4, 7, 0))))),
        If(prev == 1,
           If(curr == 0, 26,
              If(curr == 1, 0,
                 If(curr == 2, 22,
                    If(curr == 3, 7,
                       If(curr == 4, 24, 0))))),
           If(prev == 2,
              If(curr == 0, 9,
                 If(curr == 1, 22,
                    If(curr == 2, 0,
                       If(curr == 3, 20,
                          If(curr == 4, 10, 0))))),
              If(prev == 3,
                 If(curr == 0, 22,
                    If(curr == 1, 9,
                       If(curr == 2, 21,
                          If(curr == 3, 0,
                             If(curr == 4, 17, 0))))),
                 If(prev == 4,
                    If(curr == 0, 8,
                       If(curr == 1, 22,
                          If(curr == 2, 7,
                             If(curr == 3, 18,
                                If(curr == 4, 0, 0))))),
                    0)))))
    solver.add(arrival[i] == departure[i-1] + travel_time_expr)

# Add constraints for start and end times
for i in range(5):
    friend = friends[order[i]]
    earliest = friend['earliest']
    latest = friend['latest']
    duration = friend['duration']
    start_i = If(arrival[i] >= earliest, arrival[i], earliest)
    solver.add(departure[i] == start_i + duration)
    solver.add(departure[i] <= latest)

# Solve and extract solution
if solver.check() == sat:
    model = solver.model()
    order_values = [model.evaluate(order[i]).as_long() for i in range(5)]
    itinerary = []
    for i in range(5):
        friend_index = order_values[i]
        friend = friends[friend_index]
        arrival_i_val = model.evaluate(arrival[i]).as_long()
        earliest = friend['earliest']
        start_i_val = max(arrival_i_val, earliest)
        duration = friend['duration']
        end_i_val = start_i_val + duration
        name = friend['name']
        start_str = to_time_str(start_i_val)
        end_str = to_time_str(end_i_val)
        itinerary.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")