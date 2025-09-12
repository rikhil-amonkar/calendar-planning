from z3 import *

def minutes_to_time_str(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

# Define friends' data
friend_data = [
    {'name': 'Nancy', 'available_start': 9*60 + 30, 'available_end': 13*60 + 30, 'min_duration': 90},
    {'name': 'Mary', 'available_start': 7*60, 'available_end': 21*60, 'min_duration': 75},
    {'name': 'Jessica', 'available_start': 11*60 + 15, 'available_end': 13*60 + 45, 'min_duration': 45}
]

# Friend travel matrix (friend index to friend index)
friend_travel_matrix = [
    [0, 17, 22],
    [16, 0, 16],
    [18, 16, 0]
]

# Travel time from Financial District to each friend's location
fd_to_friend_travel = [5, 17, 19]

# Initial time (9:00 AM in minutes)
initial_time = 9 * 60  # 540 minutes

# Create Z3 solver
solver = Solver()

# Define sequence variables (0: Nancy, 1: Mary, 2: Jessica)
seq0 = Int('seq0')
seq1 = Int('seq1')
seq2 = Int('seq2')

# Add constraints for sequence variables (0-2, distinct)
solver.add(And(0 <= seq0, seq0 <= 2, 0 <= seq1, seq1 <= 2, 0 <= seq2, seq2 <= 2))
solver.add(Distinct(seq0, seq1, seq2))

# Define start and end time variables for each meeting
start = [Int(f'start_{i}') for i in range(3)]
end = [Int(f'end_{i}') for i in range(3)]

# Add constraints for each meeting
for i in range(3):
    if i == 0:
        friend_index = seq0
        # Arrival time for first meeting
        arrival_time = initial_time + If(friend_index == 0, 5, If(friend_index == 1, 17, 19))
    elif i == 1:
        # Previous friend is seq0, current is seq1
        prev = seq0
        curr = seq1
        # Compute travel time between prev and curr
        travel_time = If(prev == 0,
                         If(curr == 0, 0,
                            If(curr == 1, 17, 22)),
                         If(prev == 1,
                            If(curr == 0, 16,
                               If(curr == 1, 0, 16)),
                            If(prev == 2,
                               If(curr == 0, 18,
                                  If(curr == 1, 16, 0)),
                               0)))
        arrival_time = end[0] + travel_time
    else:  # i == 2
        # Previous friend is seq1, current is seq2
        prev = seq1
        curr = seq2
        # Compute travel time between prev and curr
        travel_time = If(prev == 0,
                         If(curr == 0, 0,
                            If(curr == 1, 17, 22)),
                         If(prev == 1,
                            If(curr == 0, 16,
                               If(curr == 1, 0, 16)),
                            If(prev == 2,
                               If(curr == 0, 18,
                                  If(curr == 1, 16, 0)),
                               0)))
        arrival_time = end[1] + travel_time

    # Determine friend's available_start, available_end, min_duration based on friend index
    if i == 0:
        friend_index_var = seq0
    elif i == 1:
        friend_index_var = seq1
    else:
        friend_index_var = seq2

    # Available start time
    available_start = If(friend_index_var == 0, 9*60 + 30,
                           If(friend_index_var == 1, 7*60,
                              11*60 + 15))
    # Available end time
    available_end = If(friend_index_var == 0, 13*60 + 30,
                         If(friend_index_var == 1, 21*60,
                            13*60 + 45))
    # Minimum duration
    min_duration = If(friend_index_var == 0, 90,
                        If(friend_index_var == 1, 75, 45))

    # Add constraints
    solver.add(start[i] >= arrival_time)
    solver.add(start[i] >= available_start)
    solver.add(end[i] >= start[i] + min_duration)
    solver.add(end[i] <= available_end)

# Check for solution
if solver.check() == sat:
    model = solver.model()
    # Extract sequence and times
    sequence = [model.eval(seq0).as_long(), model.eval(seq1).as_long(), model.eval(seq2).as_long()]
    starts = [model.eval(start[i]).as_long() for i in range(3)]
    ends = [model.eval(end[i]).as_long() for i in range(3)]

    # Build itinerary
    itinerary = []
    for i in range(3):
        friend_idx = sequence[i]
        name = friend_data[friend_idx]['name']
        location = ['Chinatown', 'Alamo Square', 'Bayview'][friend_idx]
        start_time = starts[i]
        end_time = ends[i]
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": minutes_to_time_str(start_time),
            "end_time": minutes_to_time_str(end_time)
        })

    # Output JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")