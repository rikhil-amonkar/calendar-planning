import itertools
from z3 import *

# Meetings data: name, location, start window (minutes from 9:00 AM), end window, minimum duration
meetings_info = [
    {"name": "Ronald", "start_win": 60, "end_win": 480, "min_dur": 105, "index": 0},
    {"name": "Helen", "start_win": 270, "end_win": 480, "min_dur": 120, "index": 1},
    {"name": "Joshua", "start_win": 315, "end_win": 630, "min_dur": 90, "index": 2},
    {"name": "Margaret", "start_win": 75, "end_win": 780, "min_dur": 60, "index": 3}
]

# Travel time from Pacific Heights to each meeting location
T_base = [8, 16, 21, 11]  # Ronald, Helen, Joshua, Margaret

# Travel time matrix between meeting locations (indices: 0-Ronald, 1-Helen, 2-Joshua, 3-Margaret)
T = [
    [0, 17, 25, 13],
    [17, 0, 17, 6],
    [25, 17, 0, 15],
    [13, 6, 15, 0]
]

# We are skipping Sarah because it's impossible to meet her for 45 minutes within her availability window.

# Try to schedule subsets of meetings in descending order of size
solution_found = False
result_itinerary = []

# Iterate over subset sizes from 4 down to 1
for num_meetings in range(4, 0, -1):
    if solution_found:
        break
    # Generate all combinations of meetings of size num_meetings
    for chosen_indices in itertools.combinations(range(4), num_meetings):
        s = Solver()
        
        # Create variables for start and end times for all meetings (even if not chosen, but we'll ignore those)
        s0, s1, s2, s3 = Ints('s0 s1 s2 s3')
        e0, e1, e2, e3 = Ints('e0 e1 e2 e3')
        start_vars = [s0, s1, s2, s3]
        end_vars = [e0, e1, e2, e3]
        
        # Define end times in terms of start times and minimum durations
        s.add(e0 == s0 + 105)
        s.add(e1 == s1 + 120)
        s.add(e2 == s2 + 90)
        s.add(e3 == s3 + 60)
        
        # Create arrays for start and end times for Z3
        start_arr = Array('start_arr', IntSort(), IntSort())
        end_arr = Array('end_arr', IntSort(), IntSort())
        for i in range(4):
            s.add(start_arr[i] == start_vars[i])
            s.add(end_arr[i] == end_vars[i])
        
        # Create arrays for availability windows
        win_start_arr = Array('win_start_arr', IntSort(), IntSort())
        win_end_arr = Array('win_end_arr', IntSort(), IntSort())
        for i in range(4):
            s.add(win_start_arr[i] == meetings_info[i]['start_win'])
            s.add(win_end_arr[i] == meetings_info[i]['end_win'])
        
        # Create travel time matrix for Z3
        tt_arr = Array('tt_arr', IntSort(), IntSort(), IntSort())
        for i in range(4):
            for j in range(4):
                s.add(tt_arr[i, j] == T[i][j])
        
        # Permutation variables for the chosen meetings
        p = [Int('p_%d' % i) for i in range(num_meetings)]
        # Each permutation variable must be one of the chosen indices
        s.add(Distinct(p))
        for i in range(num_meetings):
            s.add(Or([p[i] == idx for idx in chosen_indices]))
        
        # Constraints for the first meeting in the permutation
        s.add(start_arr[p[0]] >= T_base[p[0]])
        s.add(start_arr[p[0]] >= win_start_arr[p[0]])
        
        # Constraints for the remaining meetings in the permutation
        for k in range(1, num_meetings):
            s.add(start_arr[p[k]] >= end_arr[p[k-1]] + tt_arr[p[k-1], p[k]])
            s.add(start_arr[p[k]] >= win_start_arr[p[k]])
        
        # End time constraints for chosen meetings
        for idx in chosen_indices:
            s.add(end_arr[idx] <= win_end_arr[idx])
            s.add(start_arr[idx] >= 0)  # Start time must be non-negative
        
        if s.check() == sat:
            model = s.model()
            schedule = []
            for idx in chosen_indices:
                start_val = model.evaluate(start_arr[idx]).as_long()
                end_val = model.evaluate(end_arr[idx]).as_long()
                total_minutes_start = start_val
                start_hour = 9 + total_minutes_start // 60
                start_minute = total_minutes_start % 60
                total_minutes_end = end_val
                end_hour = 9 + total_minutes_end // 60
                end_minute = total_minutes_end % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                schedule.append({
                    "action": "meet",
                    "person": meetings_info[idx]['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
            solution_found = True
            result_itinerary = schedule
            break

# Output the result
import json
print("SOLUTION:")
print(json.dumps({"itinerary": result_itinerary}))