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
    ("Karen", 2, 570, 765, 90, 0),
    ("David", 5, 540, 1080, 120, 1),
    ("Kevin", 7, 600, 1065, 120, 2),
    ("Matthew", 8, 615, 930, 45, 3),
    ("Andrew", 9, 705, 1005, 105, 4),
    ("Barbara", 3, 600, 1170, 90, 5),
    ("Nancy", 4, 1005, 1200, 105, 6),
    ("Linda", 6, 1095, 1185, 45, 7),
    ("Mark", 1, 1125, 1260, 90, 8)
]

# Extract friend indices, locations, available times, and durations
friend_indices = [f[5] for f in friends]
friend_locations = [f[1] for f in friends]
available_starts = [f[2] for f in friends]
available_ends = [f[3] for f in friends]
min_durations = [f[4] for f in friends]
friend_names = [f[0] for f in friends]

found_schedule = None

# Try subsets from size 8 down to 1
for k in range(8, 0, -1):
    for subset in itertools.combinations(range(9), k):
        s = Solver()
        order = [Int(f'order_{i}') for i in range(k)]
        
        # Order constraints: distinct and within subset
        s.add(Distinct(order))
        for i in range(k):
            s.add(Or([order[i] == idx for idx in subset]))
        
        # Start time variables for all friends (only subset is constrained)
        start_vars = [Int(f'start_{i}') for i in range(9)]
        
        # Time window constraints for friends in the subset
        for i in subset:
            s.add(start_vars[i] >= available_starts[i])
            s.add(start_vars[i] + min_durations[i] <= available_ends[i])
        
        # First meeting constraint
        first_friend = order[0]
        first_loc = friend_locations[first_friend]
        s.add(start_vars[first_friend] >= 540 + travel_matrix[0][first_loc])
        
        # Chain constraints for subsequent meetings
        for i in range(1, k):
            prev_friend = order[i-1]
            curr_friend = order[i]
            prev_loc = friend_locations[prev_friend]
            curr_loc = friend_locations[curr_friend]
            travel_time = travel_matrix[prev_loc][curr_loc]
            s.add(start_vars[curr_friend] >= start_vars[prev_friend] + min_durations[prev_friend] + travel_time)
        
        # Check satisfiability
        if s.check() == sat:
            model = s.model()
            schedule = []
            for i in subset:
                start_val = model.eval(start_vars[i]).as_long()
                end_val = start_val + min_durations[i]
                start_str = f"{start_val//60:02d}:{start_val%60:02d}"
                end_str = f"{end_val//60:02d}:{end_val%60:02d}"
                schedule.append((friend_names[i], start_val, start_str, end_str))
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