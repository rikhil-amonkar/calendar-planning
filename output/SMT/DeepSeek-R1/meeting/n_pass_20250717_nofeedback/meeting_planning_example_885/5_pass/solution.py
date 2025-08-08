import itertools
from z3 import *
import json

# Define travel time matrix (10x10)
# Index: 0: Russian Hill, 1: Marina, 2: Financial, 3: Alamo, 4: Golden Gate, 5: Castro, 6: Bayview, 7: Sunset, 8: Haight, 9: Nob Hill
travel_matrix = [
    [0, 7, 11, 15, 21, 21, 23, 23, 17, 5],
    [8, 0, 17, 15, 18, 22, 27, 19, 16, 12],
    [11, 15, 0, 17, 23, 20, 19, 30, 19, 8],
    [13, 15, 17, 0, 9, 8, 16, 16, 5, 11],
    [19, 16, 26, 9, 0, 13, 23, 10, 7, 20],
    [18, 21, 21, 8, 11, 0, 19, 17, 6, 16],
    [23, 27, 19, 16, 22, 19, 0, 23, 19, 20],
    [24, 21, 30, 17, 11, 17, 22, 0, 15, 27],
    [17, 17, 21, 5, 7, 6, 18, 15, 0, 15],
    [5, 11, 9, 11, 17, 17, 19, 24, 13, 0]
]

# Friend data: (name, location_index, available_start_min, available_end_min, min_duration, friend_index)
friends = [
    ("Karen", 2, 570, 765, 90, 0),      # 9:30AM to 12:45PM
    ("David", 5, 540, 1080, 120, 1),    # 9:00AM to 6:00PM
    ("Kevin", 7, 600, 1065, 120, 2),    # 10:00AM to 5:45PM
    ("Matthew", 8, 615, 930, 45, 3),    # 10:15AM to 3:30PM
    ("Andrew", 9, 705, 1005, 105, 4),   # 11:45AM to 4:45PM
    ("Barbara", 3, 600, 1170, 90, 5),   # 10:00AM to 7:30PM
    ("Nancy", 4, 1005, 1200, 105, 6),   # 4:45PM to 8:00PM
    ("Linda", 6, 1095, 1185, 45, 7),    # 6:15PM to 7:45PM
    ("Mark", 1, 1125, 1260, 90, 8)      # 6:45PM to 9:00PM
]

friend_names = [f[0] for f in friends]
friend_locations = [f[1] for f in friends]
available_starts = [f[2] for f in friends]
available_ends = [f[3] for f in friends]
min_durations = [f[4] for f in friends]

# Precompute travel_from_start: from Russian Hill (0) to each friend's location
travel_from_start = [travel_matrix[0][loc] for loc in friend_locations]

# Precompute travel_between_friends: between each pair of friends
travel_between_friends = [[travel_matrix[friend_locations[i]][friend_locations[j]] for j in range(9)] for i in range(9)]

found_schedule = None

# Try subsets from size 8 down to 1
for k in range(8, 0, -1):
    for subset in itertools.combinations(range(9), k):
        s = Solver()
        
        # Create Z3 variables for start times and meeting order
        start_times = [Int(f'start_{i}') for i in range(k)]
        order = [Int(f'order_{i}') for i in range(k)]
        
        # Order must be a permutation of the subset
        s.add(Distinct(order))
        for i in range(k):
            s.add(Or([order[i] == idx for idx in subset]))
        
        # Time window constraints for each meeting
        for i in range(k):
            friend_idx = order[i]
            s.add(start_times[i] >= available_starts[friend_idx])
            s.add(start_times[i] + min_durations[friend_idx] <= available_ends[friend_idx])
        
        # First meeting constraint: start time >= 9:00AM (540) + travel from start
        s.add(start_times[0] >= 540 + travel_from_start[order[0]])
        
        # Constraints for consecutive meetings
        for i in range(k-1):
            # Apply travel time constraints using implications
            for a in subset:
                for b in subset:
                    if a != b:
                        s.add(Implies(And(order[i] == a, order[i+1] == b),
                                      start_times[i+1] >= start_times[i] + min_durations[a] + travel_between_friends[a][b]))
        
        # Check satisfiability
        if s.check() == sat:
            model = s.model()
            schedule = []
            # Extract meeting details
            for i in range(k):
                friend_idx = model.eval(order[i]).as_long()
                start_val = model.eval(start_times[i]).as_long()
                duration = min_durations[friend_idx]
                end_val = start_val + duration
                start_str = f"{start_val//60:02d}:{start_val%60:02d}"
                end_str = f"{end_val//60:02d}:{end_val%60:02d}"
                schedule.append((friend_names[friend_idx], start_val, start_str, end_str))
            # Sort meetings by start time
            schedule.sort(key=lambda x: x[1])
            itinerary = [{"action": "meet", "person": name, "start_time": start, "end_time": end} for name, _, start, end in schedule]
            found_schedule = {"itinerary": itinerary}
            break
    if found_schedule:
        break

# Output the result
if found_schedule:
    print(json.dumps(found_schedule, indent=2))
else:
    print('{"itinerary": []}')