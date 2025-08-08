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
    ("Daniel", "Nob Hill", 0, 120, 15),          # 9:00 AM - 11:00 AM
    ("Betty", "Richmond District", 255, 405, 30), # 1:15 PM - 3:45 PM
    ("Kevin", "Chinatown", 180, 600, 30),         # 12:00 PM - 7:00 PM
    ("Timothy", "Pacific Heights", 180, 540, 90), # 12:00 PM - 6:00 PM
    ("Steven", "Marina District", 450, 705, 90),  # 4:30 PM - 8:45 PM
    ("Lisa", "The Castro", 615, 735, 120),        # 7:15 PM - 9:15 PM
    ("Ashley", "Golden Gate Park", 705, 765, 60), # 8:45 PM - 9:45 PM
    ("Elizabeth", "Presidio", 735, 795, 45)       # 9:15 PM - 10:15 PM
]

# Initialize Z3 solver
s = Optimize()

# Create variables for each friend
meet_vars = []      # Whether meeting occurs
start_vars = []     # Start time (minutes from 9:00 AM)
end_vars = []       # End time (start + duration)
locations = []      # Location of meeting
names = []          # Friend's name

# Add dummy meeting at start (Mission District, 9:00 AM)
meet_vars.append(True)
start_vars.append(0)
end_vars.append(0)
locations.append("Mission District")
names.append("start")

# Create variables for friends
for name, loc, win_start, win_end, dur in friends:
    meet_var = Bool(f'meet_{name}')
    start_var = Int(f'start_{name}')
    end_var = Int(f'end_{name}')
    
    meet_vars.append(meet_var)
    start_vars.append(start_var)
    end_vars.append(end_var)
    locations.append(loc)
    names.append(name)
    
    # Duration and time window constraints
    s.add(If(meet_var, end_var == start_var + dur, True))
    s.add(Implies(meet_var, And(start_var >= win_start, end_var <= win_end, start_var >= 0)))

# Create order variables for sequencing
order_vars = [Int(f'order_{i}') for i in range(len(meet_vars))]
s.add(order_vars[0] == 0)  # Dummy meeting is always first

# Order constraints for friend meetings
for i in range(1, len(meet_vars)):
    s.add(If(meet_vars[i], 
             And(order_vars[i] >= 1, order_vars[i] < len(meet_vars)), 
             order_vars[i] == -1))
    
# All selected meetings have distinct positive orders
s.add(Distinct([If(meet_vars[i], order_vars[i], -i) for i in range(len(meet_vars))]))

# Sequence constraints
for i in range(len(meet_vars)):
    for j in range(1, len(meet_vars)):
        if i == j:
            continue
        # If both meetings selected and j comes immediately after i
        cond = And(meet_vars[i], meet_vars[j], order_vars[j] == order_vars[i] + 1)
        # Ensure travel time between consecutive meetings
        s.add(Implies(cond, start_vars[j] >= end_vars[i] + travel_times[locations[i]][locations[j]]))

# Objective: maximize number of meetings
s.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(1, len(meet_vars))]))

# Solve the problem
if s.check() == sat:
    model = s.model()
    scheduled_meetings = []
    for i in range(1, len(meet_vars)):
        if is_true(model[meet_vars[i]]):
            start_val = model.evaluate(start_vars[i])
            start_min = start_val.as_long() if isinstance(start_val, IntNumRef) else 0
            dur = friends[i-1][4]
            end_min = start_min + dur

            # Convert to HH:MM format
            start_hour = 9 + start_min // 60
            start_minute = start_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            
            end_hour = 9 + end_min // 60
            end_minute = end_min % 60
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            
            scheduled_meetings.append((start_min, names[i], start_str, end_str))
    
    # Sort meetings by start time
    scheduled_meetings.sort(key=lambda x: x[0])
    itinerary = [{"action": "meet", "person": name, "start_time": st, "end_time": et} 
                 for _, name, st, et in scheduled_meetings]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')