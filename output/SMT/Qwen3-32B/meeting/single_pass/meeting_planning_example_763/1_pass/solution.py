import z3
import json

# Define friends
friends = [
    {'name': 'Richard', 'location': 'Embarcadero', 'available_start': 195, 'available_end': 405, 'duration': 90},
    {'name': 'Mark', 'location': 'Pacific Heights', 'available_start': 180, 'available_end': 300, 'duration': 45},
    {'name': 'Matthew', 'location': 'Russian Hill', 'available_start': 330, 'available_end': 540, 'duration': 90},
    {'name': 'Rebecca', 'location': 'Haight-Ashbury', 'available_start': 165, 'available_end': 360, 'duration': 60},
    {'name': 'Melissa', 'location': 'Golden Gate Park', 'available_start': 105, 'available_end': 330, 'duration': 90},
    {'name': 'Margaret', 'location': 'Fisherman\'s Wharf', 'available_start': 165, 'available_end': 495, 'duration': 15},
    {'name': 'Emily', 'location': 'Sunset District', 'available_start': 225, 'available_end': 300, 'duration': 45},
    {'name': 'George', 'location': 'The Castro', 'available_start': 120, 'available_end': 255, 'duration': 75}
]

locations = [
    'Chinatown',
    'Embarcadero',
    'Pacific Heights',
    'Russian Hill',
    'Haight-Ashbury',
    'Golden Gate Park',
    'Fisherman\'s Wharf',
    'Sunset District',
    'The Castro'
]

# Define travel_times matrix
travel_times = [[0 for _ in range(9)] for _ in range(9)]

# Fill in the travel times
travel_times[0][1] = 5
travel_times[0][2] = 10
travel_times[0][3] = 7
travel_times[0][4] = 19
travel_times[0][5] = 23
travel_times[0][6] = 8
travel_times[0][7] = 29
travel_times[0][8] = 22

travel_times[1][0] = 7
travel_times[1][2] = 11
travel_times[1][3] = 8
travel_times[1][4] = 21
travel_times[1][5] = 25
travel_times[1][6] = 6
travel_times[1][7] = 30
travel_times[1][8] = 25

travel_times[2][0] = 11
travel_times[2][1] = 10
travel_times[2][3] = 7
travel_times[2][4] = 11
travel_times[2][5] = 15
travel_times[2][6] = 13
travel_times[2][7] = 21
travel_times[2][8] = 16

travel_times[3][0] = 9
travel_times[3][1] = 8
travel_times[3][2] = 7
travel_times[3][4] = 17
travel_times[3][5] = 21
travel_times[3][6] = 7
travel_times[3][7] = 23
travel_times[3][8] = 21

travel_times[4][0] = 19
travel_times[4][1] = 20
travel_times[4][2] = 12
travel_times[4][3] = 17
travel_times[4][5] = 7
travel_times[4][6] = 23
travel_times[4][7] = 15
travel_times[4][8] = 6

travel_times[5][0] = 23
travel_times[5][1] = 25
travel_times[5][2] = 16
travel_times[5][3] = 19
travel_times[5][4] = 7
travel_times[5][6] = 24
travel_times[5][7] = 10
travel_times[5][8] = 13

travel_times[6][0] = 12
travel_times[6][1] = 8
travel_times[6][2] = 12
travel_times[6][3] = 7
travel_times[6][4] = 22
travel_times[6][5] = 25
travel_times[6][7] = 27
travel_times[6][8] = 27

travel_times[7][0] = 30
travel_times[7][1] = 30
travel_times[7][2] = 21
travel_times[7][3] = 24
travel_times[7][4] = 15
travel_times[7][5] = 11
travel_times[7][6] = 29
travel_times[7][8] = 17

travel_times[8][0] = 22
travel_times[8][1] = 22
travel_times[8][2] = 16
travel_times[8][3] = 18
travel_times[8][4] = 6
travel_times[8][5] = 11
travel_times[8][6] = 24
travel_times[8][7] = 17

# Now, create the Z3 solver
s = z3.Optimize()

positions = 8
friends_count = 8

# Create variables
friend_pos = [z3.Int(f'friend_pos_{i}') for i in range(positions)]
start_time = [z3.Int(f'start_time_{i}') for i in range(positions)]
end_time = [z3.Int(f'end_time_{i}') for i in range(positions)]

# Define travel_time function
travel_time_func = z3.Function('travel_time', z3.IntSort(), z3.IntSort(), z3.IntSort())

# Add constraints for the travel_time function
for from_loc in range(9):
    for to_loc in range(9):
        s.add(travel_time_func(from_loc, to_loc) == travel_times[from_loc][to_loc])

# Constraints for friend_pos[i] to be between 0 and 8
for i in range(positions):
    s.add(z3.And(friend_pos[i] >= 0, friend_pos[i] <= 8))

# Constraints for uniqueness
for i in range(positions):
    for j in range(i+1, positions):
        s.add(z3.Implies(z3.And(friend_pos[i] != 0, friend_pos[j] != 0), friend_pos[i] != friend_pos[j]))

# Constraints for contiguous sequence
for i in range(1, positions):
    s.add(z3.Implies(friend_pos[i] != 0, friend_pos[i-1] != 0))

# For each position, add constraints
for i in range(positions):
    # Determine location index based on friend_pos[i]
    loc_index = z3.If(friend_pos[i] == 1, 1,
        z3.If(friend_pos[i] == 2, 2,
            z3.If(friend_pos[i] == 3, 3,
                z3.If(friend_pos[i] == 4, 4,
                    z3.If(friend_pos[i] == 5, 5,
                        z3.If(friend_pos[i] == 6, 6,
                            z3.If(friend_pos[i] == 7, 7,
                                z3.If(friend_pos[i] == 8, 8, -1)
                            )
                        )
                    )
                )
            )
        )
    )

    # Determine available_start
    avail_start = z3.If(friend_pos[i] == 1, 195,
        z3.If(friend_pos[i] == 2, 180,
            z3.If(friend_pos[i] == 3, 330,
                z3.If(friend_pos[i] == 4, 165,
                    z3.If(friend_pos[i] == 5, 105,
                        z3.If(friend_pos[i] == 6, 165,
                            z3.If(friend_pos[i] == 7, 225,
                                z3.If(friend_pos[i] == 8, 120, -1)
                            )
                        )
                    )
                )
            )
        )
    )

    # Determine duration
    duration = z3.If(friend_pos[i] == 1, 90,
        z3.If(friend_pos[i] == 2, 45,
            z3.If(friend_pos[i] == 3, 90,
                z3.If(friend_pos[i] == 4, 60,
                    z3.If(friend_pos[i] == 5, 90,
                        z3.If(friend_pos[i] == 6, 15,
                            z3.If(friend_pos[i] == 7, 45,
                                z3.If(friend_pos[i] == 8, 75, -1)
                            )
                        )
                    )
                )
            )
        )
    )

    # Determine available_end
    avail_end = z3.If(friend_pos[i] == 1, 405,
        z3.If(friend_pos[i] == 2, 300,
            z3.If(friend_pos[i] == 3, 540,
                z3.If(friend_pos[i] == 4, 360,
                    z3.If(friend_pos[i] == 5, 330,
                        z3.If(friend_pos[i] == 6, 495,
                            z3.If(friend_pos[i] == 7, 300,
                                z3.If(friend_pos[i] == 8, 255, -1)
                            )
                        )
                    )
                )
            )
        )
    )

    # Determine previous location index for i > 0
    prev_loc_index = None
    if i > 0:
        prev_loc_index = z3.If(friend_pos[i-1] == 1, 1,
            z3.If(friend_pos[i-1] == 2, 2,
                z3.If(friend_pos[i-1] == 3, 3,
                    z3.If(friend_pos[i-1] == 4, 4,
                        z3.If(friend_pos[i-1] == 5, 5,
                            z3.If(friend_pos[i-1] == 6, 6,
                                z3.If(friend_pos[i-1] == 7, 7,
                                    z3.If(friend_pos[i-1] == 8, 8, -1)
                                )
                            )
                        )
                    )
                )
            )
        )

    # Calculate arrival_time
    is_used = friend_pos[i] != 0
    arrival_time = z3.IntVal(0)
    if i == 0:
        arrival_time = 540 + travel_time_func(0, loc_index)
    else:
        arrival_time = end_time[i-1] + travel_time_func(prev_loc_index, loc_index)

    # Add constraints if used
    s.add(z3.Implies(is_used, start_time[i] >= arrival_time))
    s.add(z3.Implies(is_used, start_time[i] >= avail_start))
    s.add(z3.Implies(is_used, start_time[i] + duration <= avail_end))
    s.add(z3.Implies(is_used, end_time[i] == start_time[i] + duration))

# Objective: maximize the number of used friends
used_count = sum([z3.If(friend_pos[i] != 0, 1, 0) for i in range(positions)])
s.maximize(used_count)

# Check if the solver can find a solution
if s.check() == z3.sat:
    model = s.model()
    itinerary = []
    for i in range(positions):
        fp = model.evaluate(friend_pos[i])
        if fp.as_long() != 0:
            friend_idx = fp.as_long() - 1
            friend = friends[friend_idx]
            st = model.evaluate(start_time[i]).as_long()
            et = model.evaluate(end_time[i]).as_long()
            st_h = st // 60
            st_m = st % 60
            et_h = et // 60
            et_m = et % 60
            start_time_str = f"{st_h:02d}:{st_m:02d}"
            end_time_str = f"{et_h:02d}:{et_m:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")