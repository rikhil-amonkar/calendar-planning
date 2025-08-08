import json
from z3 import *

# Define travel times between districts
travel_times = {
    "Mission District": {
        "The Castro": 7,
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20
    },
    "The Castro": {
        "Mission District": 7,
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16
    },
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14
    },
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

# Friends data: (name, location, window_start (minutes from 9:00 AM), window_end, min_duration)
friends = [
    ("Daniel", "Nob Hill", 0, 120, 15),
    ("Betty", "Richmond District", 255, 405, 30),
    ("Kevin", "Chinatown", 180, 600, 30),
    ("Timothy", "Pacific Heights", 180, 540, 90),
    ("Steven", "Marina District", 450, 705, 90),
    ("Lisa", "The Castro", 615, 735, 120),
    ("Ashley", "Golden Gate Park", 705, 765, 60),
    ("Elizabeth", "Presidio", 735, 795, 45)
]

# Initialize Z3 optimizer
opt = Optimize()

# Meeting variables
meet_vars = []      # Boolean for whether meeting occurs
start_vars = []     # Integer start time (minutes from 9:00 AM)
end_vars = []       # End time (start + duration)
locations = []      # Location of meeting
names = []          # Friend's name

# Dummy meeting at start (Mission District, 9:00 AM)
meet_vars.append(True)
start_vars.append(0)
end_vars.append(0)
locations.append("Mission District")
names.append("start")

# Create variables for each friend
for name, loc, win_start, win_end, dur in friends:
    meet_var = Bool(f'meet_{name}')
    start_var = Int(f'start_{name}')
    end_var = start_var + dur  # End time is start time plus duration

    meet_vars.append(meet_var)
    start_vars.append(start_var)
    end_vars.append(end_var)
    locations.append(loc)
    names.append(name)

    # Constraint: if meeting occurs, it must be within the friend's window
    opt.add(Implies(meet_var, And(start_var >= win_start, end_var <= win_end)))

# Add travel constraints for all pairs of meetings (including dummy)
n = len(meet_vars)  # Total meetings (dummy + friends)
for i in range(n):
    for j in range(i + 1, n):
        # If both meetings occur, ensure non-overlapping with travel time
        opt.add(Implies(
            And(meet_vars[i], meet_vars[j]),
            Or(
                start_vars[j] >= end_vars[i] + travel_times[locations[i]][locations[j]],
                start_vars[i] >= end_vars[j] + travel_times[locations[j]][locations[i]]
            )
        ))

# Objective: maximize the number of friends met
total_meet = Sum([If(meet_vars[i], 1, 0) for i in range(1, n)])
opt.maximize(total_meet)

# Solve the problem
if opt.check() == sat:
    model = opt.model()
    scheduled_meetings = []
    for i in range(1, n):  # Skip dummy meeting
        if model.evaluate(meet_vars[i]):
            start_val = model.evaluate(start_vars[i])
            start_min = start_val.as_long()
            dur = friends[i-1][4]  # Duration of the meeting
            end_min = start_min + dur

            # Convert start time to HH:MM
            total_minutes_start = start_min
            hours_start = total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            abs_hour_start = 9 + hours_start
            start_time_str = f"{abs_hour_start:02d}:{minutes_start:02d}"

            # Convert end time to HH:MM
            total_minutes_end = end_min
            hours_end = total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            abs_hour_end = 9 + hours_end
            end_time_str = f"{abs_hour_end:02d}:{minutes_end:02d}"

            scheduled_meetings.append((start_min, names[i], start_time_str, end_time_str))
    
    # Sort meetings by start time
    scheduled_meetings.sort(key=lambda x: x[0])
    itinerary = [{"action": "meet", "person": name, "start_time": st, "end_time": et} 
                 for _, name, st, et in scheduled_meetings]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')