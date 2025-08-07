from z3 import *
import json

# Travel time dictionary
travel = {
    "Presidio": {
        "Haight-Ashbury": 15, "Nob Hill": 18, "Russian Hill": 14, "North Beach": 18, 
        "Chinatown": 21, "Union Square": 22, "Embarcadero": 20, "Financial District": 23, "Marina District": 11
    },
    "Haight-Ashbury": {
        "Presidio": 15, "Nob Hill": 15, "Russian Hill": 17, "North Beach": 19, 
        "Chinatown": 19, "Union Square": 19, "Embarcadero": 20, "Financial District": 21, "Marina District": 17
    },
    "Nob Hill": {
        "Presidio": 17, "Haight-Ashbury": 13, "Russian Hill": 5, "North Beach": 8, 
        "Chinatown": 6, "Union Square": 7, "Embarcadero": 9, "Financial District": 9, "Marina District": 11
    },
    "Russian Hill": {
        "Presidio": 14, "Haight-Ashbury": 17, "Nob Hill": 5, "North Beach": 5, 
        "Chinatown": 9, "Union Square": 10, "Embarcadero": 8, "Financial District": 11, "Marina District": 7
    },
    "North Beach": {
        "Presidio": 17, "Haight-Ashbury": 18, "Nob Hill": 7, "Russian Hill": 4, 
        "Chinatown": 6, "Union Square": 7, "Embarcadero": 6, "Financial District": 8, "Marina District": 9
    },
    "Chinatown": {
        "Presidio": 19, "Haight-Ashbury": 19, "Nob Hill": 9, "Russian Hill": 7, 
        "North Beach": 3, "Union Square": 7, "Embarcadero": 5, "Financial District": 5, "Marina District": 12
    },
    "Union Square": {
        "Presidio": 24, "Haight-Ashbury": 18, "Nob Hill": 9, "Russian Hill": 13, 
        "North Beach": 10, "Chinatown": 7, "Embarcadero": 11, "Financial District": 9, "Marina District": 18
    },
    "Embarcadero": {
        "Presidio": 20, "Haight-Ashbury": 21, "Nob Hill": 10, "Russian Hill": 8, 
        "North Beach": 5, "Chinatown": 7, "Union Square": 10, "Financial District": 5, "Marina District": 12
    },
    "Financial District": {
        "Presidio": 22, "Haight-Ashbury": 19, "Nob Hill": 8, "Russian Hill": 11, 
        "North Beach": 7, "Chinatown": 5, "Union Square": 9, "Embarcadero": 4, "Marina District": 15
    },
    "Marina District": {
        "Presidio": 10, "Haight-Ashbury": 16, "Nob Hill": 12, "Russian Hill": 8, 
        "North Beach": 11, "Chinatown": 15, "Union Square": 16, "Embarcadero": 14, "Financial District": 17
    }
}

# Meetings: (index, name, location, duration, min_start, max_end) in minutes from 9:00AM
meetings = [
    (0, "Dummy", "Presidio", 0, 0, 0),  # Start at Presidio at time 0 (9:00 AM)
    (1, "Karen", "Haight-Ashbury", 45, 720, 765),    # 9:00 PM to 9:45 PM (720 min from 9AM)
    (2, "Jessica", "Nob Hill", 90, 285, 720),        # 1:45 PM (285 min) to 9:00 PM
    (3, "Brian", "Russian Hill", 60, 390, 765),      # 3:30 PM (390 min) to 9:45 PM
    (4, "Kenneth", "North Beach", 30, 45, 720),      # 9:45 AM (45 min) to 9:00 PM
    (5, "Jason", "Chinatown", 75, 0, 165),           # 8:15 AM is -45 min? But we start at 9AM. So 8:15AM to 11:45AM: from 0 min (9AM) we have 0 to 165 min (11:45AM)
    (6, "Stephanie", "Union Square", 105, 345, 585), # 2:45 PM (345 min) to 6:45 PM (585 min)
    (7, "Kimberly", "Embarcadero", 75, 45, 630),     # 9:45 AM (45 min) to 7:30 PM (630 min)
    (8, "Steven", "Financial District", 60, 0, 735), # 7:15AM is before 9AM? But available until 9:15PM (735 min)
    (9, "Mark", "Marina District", 75, 75, 240)      # 10:15AM (75 min) to 1:00PM (240 min)
]

# Create Z3 variables
t = [0]  # t0 = 0 for dummy meeting (start at Presidio at 9:00AM)
scheduled = [None]  # no flag for dummy (always scheduled)
for i in range(1, 10):
    t.append(Int('t_%d' % i))
    scheduled.append(Bool('scheduled_%d' % i))

# Create optimizer
opt = Optimize()

# Add constraints for each meeting
for i in range(1, 10):
    name, loc, dur, min_start, max_end = meetings[i][1], meetings[i][2], meetings[i][3], meetings[i][4], meetings[i][5]
    # If scheduled, enforce time window
    opt.add(Implies(scheduled[i], And(t[i] >= min_start, t[i] + dur <= max_end)))

# Add travel constraints for each pair (i, j) with i < j
for i in range(0, 10):
    for j in range(i+1, 10):
        loc_i = meetings[i][2]
        loc_j = meetings[j][2]
        dur_i = meetings[i][3]
        dur_j = meetings[j][3]
        travel_ij = travel[loc_i][loc_j]
        travel_ji = travel[loc_j][loc_i]
        if i == 0:  # Dummy (always scheduled) at Presidio at time 0
            # For any meeting j, if scheduled, it must start at least travel time from Presidio
            opt.add(Implies(scheduled[j], t[j] >= travel_ij))
        else:
            # For two meetings that are both scheduled, they must not overlap and travel time must be considered
            opt.add(Implies(And(scheduled[i], scheduled[j]),
                            Or(t[j] >= t[i] + dur_i + travel_ij,
                               t[i] >= t[j] + dur_j + travel_ji)
            ))

# Maximize the number of scheduled meetings
total_scheduled = Sum([If(scheduled[i], 1, 0) for i in range(1, 10)])
opt.maximize(total_scheduled)

# Solve and output
if opt.check() == sat:
    m = opt.model()
    scheduled_meetings = []
    for i in range(1, 10):
        if m.evaluate(scheduled[i]):
            start_min = m.evaluate(t[i])
            if isinstance(start_min, IntNumRef):
                start_val = start_min.as_long()
            else:
                start_val = start_min
            name = meetings[i][1]
            dur = meetings[i][3]
            end_val = start_val + dur
            # Convert minutes to time from 9:00AM
            start_hour = 9 + start_val // 60
            start_minute = start_val % 60
            end_hour = 9 + end_val // 60
            end_minute = end_val % 60
            start_time = f"{start_hour:02d}:{start_minute:02d}"
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            scheduled_meetings.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort by start time
    scheduled_meetings.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
    print('SOLUTION:')
    print(json.dumps({"itinerary": scheduled_meetings}))
else:
    print("No solution found")