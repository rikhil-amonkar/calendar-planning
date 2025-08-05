from z3 import *
import itertools
import json

# Define travel times between locations (6x6 matrix)
travel_matrix = [
    [0, 7, 18, 23, 12, 22],   # Presidio
    [7, 0, 17, 22, 9, 21],    # Richmond District
    [17, 18, 0, 8, 22, 7],    # North Beach
    [22, 21, 7, 0, 23, 9],    # Financial District
    [11, 7, 24, 26, 0, 22],   # Golden Gate Park
    [24, 20, 10, 9, 22, 0]    # Union Square
]

# Define meeting information
meeting_info = [
    {   # Jason
        "name": "Jason",
        "loc": 1,  # Richmond District
        "dur": 90,
        "avail_start": 240,  # 13:00 (4h from 9:00)
        "avail_end": 705     # 20:45 (11h45m from 9:00)
    },
    {   # Melissa
        "name": "Melissa",
        "loc": 2,  # North Beach
        "dur": 45,
        "avail_start": 585,  # 18:45 (9h45m from 9:00)
        "avail_end": 675     # 20:15 (11h15m from 9:00)
    },
    {   # Brian
        "name": "Brian",
        "loc": 3,  # Financial District
        "dur": 15,
        "avail_start": 45,   # 9:45 (45m from 9:00)
        "avail_end": 765     # 21:45 (12h45m from 9:00)
    },
    {   # Elizabeth
        "name": "Elizabeth",
        "loc": 4,  # Golden Gate Park
        "dur": 105,
        "avail_start": 0,    # 8:45AM (set to 0 since we start at 9:00)
        "avail_end": 750     # 21:30 (12h30m from 9:00)
    },
    {   # Laura
        "name": "Laura",
        "loc": 5,  # Union Square
        "dur": 75,
        "avail_start": 315,  # 14:15 (5h15m from 9:00)
        "avail_end": 630     # 19:30 (10h30m from 9:00)
    }
]

found_solution = False
solution_schedule = []

# Try to meet all 5 friends first, then 4, etc.
for k in range(5, 0, -1):
    if found_solution:
        break
    # Check all combinations of k friends
    for subset in itertools.combinations(range(5), k):
        if found_solution:
            break
        # Check all meeting orders
        for perm in itertools.permutations(subset):
            s = Solver()
            start_vars = [Int(f's_{i}') for i in range(len(perm))]
            
            # Constraints for first meeting
            first_meeting = meeting_info[perm[0]]
            s.add(start_vars[0] >= travel_matrix[0][first_meeting['loc']])
            s.add(start_vars[0] >= first_meeting['avail_start'])
            s.add(start_vars[0] + first_meeting['dur'] <= first_meeting['avail_end'])
            
            # Constraints for subsequent meetings
            for j in range(1, len(perm)):
                prev_meeting = meeting_info[perm[j-1]]
                curr_meeting = meeting_info[perm[j]]
                travel_time = travel_matrix[prev_meeting['loc']][curr_meeting['loc']]
                s.add(start_vars[j] >= start_vars[j-1] + prev_meeting['dur'] + travel_time)
                s.add(start_vars[j] >= curr_meeting['avail_start'])
                s.add(start_vars[j] + curr_meeting['dur'] <= curr_meeting['avail_end'])
            
            # Check if schedule is feasible
            if s.check() == sat:
                model = s.model()
                current_schedule = []
                for idx, meeting_idx in enumerate(perm):
                    start_val = model.eval(start_vars[idx]).as_long()
                    # Convert to time from midnight (9:00 AM = 540 minutes)
                    total_minutes = 540 + start_val
                    hours = total_minutes // 60
                    minutes = total_minutes % 60
                    start_time = f"{hours:02d}:{minutes:02d}"
                    
                    end_val = start_val + meeting_info[meeting_idx]['dur']
                    total_end_minutes = 540 + end_val
                    hours_end = total_end_minutes // 60
                    minutes_end = total_end_minutes % 60
                    end_time = f"{hours_end:02d}:{minutes_end:02d}"
                    
                    current_schedule.append({
                        "action": "meet",
                        "person": meeting_info[meeting_idx]['name'],
                        "start_time": start_time,
                        "end_time": end_time
                    })
                
                solution_schedule = current_schedule
                found_solution = True
                break

# Prepare output
output = {"itinerary": solution_schedule}
print("SOLUTION:")
print(json.dumps(output))