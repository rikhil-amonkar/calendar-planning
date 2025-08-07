from z3 import *

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

# Meetings: (index, name, location, duration, min_start, max_end)
meetings = [
    (0, "Dummy", "Presidio", 0, 0, 0),
    (1, "Karen", "Haight-Ashbury", 45, 720, 765),
    (2, "Jessica", "Nob Hill", 90, 285, 720),
    (3, "Brian", "Russian Hill", 60, 390, 765),
    (4, "Kenneth", "North Beach", 30, 45, 720),
    (5, "Jason", "Chinatown", 75, 0, 165),
    (6, "Stephanie", "Union Square", 105, 345, 585),
    (7, "Kimberly", "Embarcadero", 75, 45, 630),
    (8, "Steven", "Financial District", 60, 0, 735),
    (9, "Mark", "Marina District", 75, 75, 240)
]

# Create Z3 variables
t = [0]  # t0 = 0 for dummy
scheduled = [None]  # no flag for dummy
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
        if i == 0:  # Dummy (always scheduled)
            opt.add(Implies(scheduled[j], t[j] >= travel_ij))
        else:
            opt.add(Implies(And(scheduled[i], scheduled[j]), 
                          Or(t[j] >= t[i] + dur_i + travel_ij, 
                             t[i] >= t[j] + dur_j + travel_ji))))

# Maximize the number of scheduled meetings
total_scheduled = Sum([If(scheduled[i], 1, 0) for i in range(1, 10)])
opt.maximize(total_scheduled)

# Solve
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
            hours = start_val // 60
            minutes = start_val % 60
            start_time = f"{9 + hours:02d}:{minutes:02d}"
            end_hours = end_val // 60
            end_minutes = end_val % 60
            end_time = f"{9 + end_hours:02d}:{end_minutes:02d}"
            scheduled_meetings.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort by start time
    scheduled_meetings.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
    print('SOLUTION:')
    print('{"itinerary": ' + json.dumps(scheduled_meetings) + '}')
else:
    print("No solution found")