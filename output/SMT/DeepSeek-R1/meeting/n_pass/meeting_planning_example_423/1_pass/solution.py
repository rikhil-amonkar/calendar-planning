from z3 import *
import itertools
import json

# Define the travel time matrix (6x6: Presidio, Richmond District, North Beach, Financial District, Golden Gate Park, Union Square)
travel_matrix = [
    [0, 7, 18, 23, 12, 22],
    [7, 0, 17, 22, 9, 21],
    [17, 18, 0, 8, 22, 7],
    [22, 21, 7, 0, 23, 9],
    [11, 7, 24, 26, 0, 22],
    [24, 20, 10, 9, 22, 0]
]

# Define meeting information
meeting_info = [
    {   # Jason
        "name": "Jason",
        "loc": 1,  # Richmond District
        "dur": 90,
        "avail_start": 240,  # 13:00 (4 hours from 9:00)
        "avail_end": 705     # 20:45 (11 hours 45 minutes from 9:00)
    },
    {   # Melissa
        "name": "Melissa",
        "loc": 2,  # North Beach
        "dur": 45,
        "avail_start": 585,  # 18:45 (9 hours 45 minutes from 9:00)
        "avail_end": 675     # 20:15 (11 hours 15 minutes from 9:00)
    },
    {   # Brian
        "name": "Brian",
        "loc": 3,  # Financial District
        "dur": 15,
        "avail_start": 45,   # 9:45 (45 minutes from 9:00)
        "avail_end": 765     # 21:45 (12 hours 45 minutes from 9:00)
    },
    {   # Elizabeth
        "name": "Elizabeth",
        "loc": 4,  # Golden Gate Park
        "dur": 105,
        "avail_start": 0,    # 8:45AM, but earliest start is 9:00 + travel time
        "avail_end": 750     # 21:30 (12 hours 30 minutes from 9:00)
    },
    {   # Laura
        "name": "Laura",
        "loc": 5,  # Union Square
        "dur": 75,
        "avail_start": 315,  # 14:15 (5 hours 15 minutes from 9:00)
        "avail_end": 630     # 19:30 (10 hours 30 minutes from 9:00)
    }
]

found_solution = False
solution_schedule = []

# Try subsets from size 5 down to 1
for k in range(5, 0, -1):
    if found_solution:
        break
    for subset in itertools.combinations(range(5), k):
        if found_solution:
            break
        for perm in itertools.permutations(subset):
            s = Solver()
            start_vars = [Int(f's_{i}') for i in range(len(perm))]
            
            # First meeting constraints
            first_meeting = meeting_info[perm[0]]
            s.add(start_vars[0] >= travel_matrix[0][first_meeting['loc']])
            s.add(start_vars[0] >= first_meeting['avail_start'])
            s.add(start_vars[0] + first_meeting['dur'] <= first_meeting['avail_end'])
            
            # Subsequent meetings
            for j in range(1, len(perm)):
                prev_meeting = meeting_info[perm[j-1]]
                curr_meeting = meeting_info[perm[j]]]
                travel_time = travel_matrix[prev_meeting['loc']][curr_meeting['loc']]
                s.add(start_vars[j] >= start_vars[j-1] + prev_meeting['dur'] + travel_time)
                s.add(start_vars[j] >= curr_meeting['avail_start'])
                s.add(start_vars[j] + curr_meeting['dur'] <= curr_meeting['avail_end'])
            
            if s.check() == sat:
                model = s.model()
                current_schedule = []
                for idx, meeting_idx in enumerate(perm):
                    start_val = model.eval(start_vars[idx]).as_long()
                    total_minutes_from_midnight = 540 + start_val  # 9:00 AM is 540 minutes from midnight
                    hours = total_minutes_from_midnight // 60
                    minutes = total_minutes_from_midnight % 60
                    start_time = f"{hours:02d}:{minutes:02d}"
                    
                    end_val = start_val + meeting_info[meeting_idx]['dur']
                    total_end_minutes_from_midnight = 540 + end_val
                    hours_end = total_end_minutes_from_midnight // 60
                    minutes_end = total_end_minutes_from_midnight % 60
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

# Prepare the output
output = {"itinerary": solution_schedule}
print("SOLUTION:")
print(json.dumps(output))