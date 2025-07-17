from z3 import *
import itertools

# Define travel times dictionary
travel_dict = {
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 25,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Sunset District"): 15
}

def travel_time_between(loc1, loc2):
    return travel_dict[(loc1, loc2)]

# Define meetings
meetings = [
    {
        "name": "Ronald",
        "loc": "Nob Hill",
        "duration": 105,
        "min_start": 60,
        "max_end": 480
    },
    {
        "name": "Helen",
        "loc": "The Castro",
        "duration": 120,
        "min_start": 270,
        "max_end": 480
    },
    {
        "name": "Joshua",
        "loc": "Sunset District",
        "duration": 90,
        "min_start": 315,
        "max_end": 630
    },
    {
        "name": "Margaret",
        "loc": "Haight-Ashbury",
        "duration": 60,
        "min_start": 75,
        "max_end": 780
    }
]

all_indices = [0, 1, 2, 3]
found_schedule = None
found_combination = None

# Try from 4 down to 1 meetings
for num in range(4, 0, -1):
    for combination in itertools.combinations(all_indices, num):
        s = Solver()
        pos_vars = {}
        start_vars = {}
        end_vars = {}
        for idx in combination:
            pos_vars[idx] = Int(f'p_{idx}')
            start_vars[idx] = Int(f's_{idx}')
            end_vars[idx] = start_vars[idx] + meetings[idx]["duration"]
        
        # Position constraints: distinct and within [0, num-1]
        s.add([And(pos_vars[idx] >= 0, pos_vars[idx] < num) for idx in combination])
        s.add(Distinct([pos_vars[idx] for idx in combination]))
        
        # Availability constraints
        for idx in combination:
            s.add(start_vars[idx] >= meetings[idx]["min_start"])
            s.add(end_vars[idx] <= meetings[idx]["max_end"])
        
        # Constraints for the first meeting in the sequence
        for idx in combination:
            s.add(If(pos_vars[idx] == 0, 
                     start_vars[idx] >= travel_time_between("Pacific Heights", meetings[idx]["loc"]), 
                     True))
        
        # Constraints for consecutive meetings
        for idx_i in combination:
            for idx_j in combination:
                if idx_i != idx_j:
                    s.add(If(pos_vars[idx_i] == pos_vars[idx_j] - 1,
                             start_vars[idx_j] >= end_vars[idx_i] + travel_time_between(meetings[idx_i]["loc"], meetings[idx_j]["loc"]),
                             True))
        
        if s.check() == sat:
            model = s.model()
            found_schedule = model
            found_combination = combination
            break
    if found_schedule is not None:
        break

# Output the solution
print("SOLUTION:")
if found_schedule is None:
    print("We can meet 0 friends.")
else:
    num_meetings = len(found_combination)
    friend_names = [meetings[idx]["name"] for idx in found_combination]
    print(f"We can meet {num_meetings} friends: {', '.join(friend_names)}")
    
    schedule_details = []
    for idx in found_combination:
        pos_val = found_schedule.eval(pos_vars[idx]).as_long()
        start_val = found_schedule.eval(start_vars[idx]).as_long()
        end_val = start_val + meetings[idx]["duration"]
        name = meetings[idx]["name"]
        loc = meetings[idx]["loc"]
        schedule_details.append((pos_val, name, loc, start_val, end_val))
    
    schedule_details.sort(key=lambda x: x[0])
    
    for pos_val, name, loc, start_val, end_val in schedule_details:
        start_hour = 9 + start_val // 60
        start_min = start_val % 60
        end_hour = 9 + end_val // 60
        end_min = end_val % 60
        start_ampm = "AM" if start_hour < 12 else "PM"
        end_ampm = "AM" if end_hour < 12 else "PM"
        if start_hour > 12:
            start_hour -= 12
        if end_hour > 12:
            end_hour -= 12
        print(f"Meet {name} at {loc} from {start_hour}:{start_min:02d} {start_ampm} to {end_hour}:{end_min:02d} {end_ampm}")