from z3 import *
import json
from itertools import combinations

# Times are in minutes from midnight.
# For reference: 9:00AM = 540, 8:15AM = 495, 11:00AM = 660, etc.

# Travel times between locations (in minutes)
# Note: The keys in the inner dictionaries must match the location names in friend info.
travel = {
    "Mission District": {
        "The Castro": 7, 
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20,
    },
    "The Castro": {
        "Mission District": 7, 
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16,
    },
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14,
    },
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7,
    },
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11,
    },
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12,
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7,
    },
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Richmond District": 20,
    },
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20,
    }
}

# Friend meeting details.
# Each friend is associated with:
#  "loc": location where the meeting takes place,
#  "start": earliest available time (in minutes from midnight),
#  "end": latest available time,
#  "duration": minimum meeting duration (in minutes)
friends = {
    "Daniel":    {"loc": "Nob Hill",         "start": 495,  "end": 660,  "duration": 15},   # 8:15AM-11:00AM
    "Lisa":      {"loc": "The Castro",       "start": 1155, "end": 1275, "duration": 120},  # 19:15-21:15
    "Elizabeth": {"loc": "Presidio",         "start": 1275, "end": 1335, "duration": 45},   # 21:15-22:15
    "Steven":    {"loc": "Marina District",  "start": 990,  "end": 1245, "duration": 90},   # 16:30-20:45
    "Timothy":   {"loc": "Pacific Heights",  "start": 720,  "end": 1080, "duration": 90},   # 12:00-18:00
    "Ashley":    {"loc": "Golden Gate Park", "start": 1245, "end": 1305, "duration": 60},   # 20:45-21:45
    "Kevin":     {"loc": "Chinatown",        "start": 720,  "end": 1140, "duration": 30},   # 12:00-19:00
    "Betty":     {"loc": "Richmond District","start": 795,  "end": 945,  "duration": 30}    # 13:15-15:45
}

# Arrival at Mission District at 9:00AM (540 minutes after midnight)
arrival_time = 540

opt = Optimize()

attend = {}
start_vars = {}
end_vars = {}

# Create variables for each meeting
for name, info in friends.items():
    attend[name] = Bool("attend_" + name)
    start_vars[name] = Int("start_" + name)
    end_vars[name] = Int("end_" + name)
    # If meeting is attended then its start/end must be within friend's available window
    opt.add(Implies(attend[name], start_vars[name] >= info["start"]))
    opt.add(Implies(attend[name], end_vars[name] <= info["end"]))
    # Meeting must last at least the required duration.
    opt.add(Implies(attend[name], end_vars[name] - start_vars[name] >= info["duration"]))
    # A meeting can't start before you can travel from Mission District.
    # (Even if it is not the first meeting, this constraint is safe.)
    opt.add(Implies(attend[name],
                    start_vars[name] >= arrival_time + travel["Mission District"][info["loc"]]))
    # If not attending, set times to 0 (arbitrary, to avoid them interfering)
    opt.add(Implies(Not(attend[name]), start_vars[name] == 0))
    opt.add(Implies(Not(attend[name]), end_vars[name] == 0))

# For any two meetings that are attended, impose a disjunctive ordering constraint 
# that accounts for travel time between their locations.
for f1, f2 in combinations(friends.keys(), 2):
    loc1 = friends[f1]["loc"]
    loc2 = friends[f2]["loc"]
    t1_to_2 = travel[loc1][loc2]
    t2_to_1 = travel[loc2][loc1]
    # If both meetings are attended then either f1 happens before f2 or vice versa.
    opt.add(Implies(And(attend[f1], attend[f2]),
                    Or(end_vars[f1] + t1_to_2 <= start_vars[f2],
                       end_vars[f2] + t2_to_1 <= start_vars[f1])))

# Our objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(attend[name], 1, 0) for name in friends.keys()]))

# Check for a solution.
if opt.check() == sat:
    model = opt.model()
    # Extract attended meetings and sort them by their start time.
    schedule = []
    for name in friends.keys():
        if model.eval(attend[name]):
            s = model.eval(start_vars[name]).as_long()
            e = model.eval(end_vars[name]).as_long()
            schedule.append((s, e, name))
    schedule.sort(key=lambda x: x[0])
    
    # Helper to convert minutes to HH:MM formatted string.
    def minutes_to_HHMM(m):
        h = m // 60
        m_mod = m % 60
        return f"{h:02d}:{m_mod:02d}"
    
    itinerary = []
    for s, e, name in schedule:
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_HHMM(s),
            "end_time": minutes_to_HHMM(e)
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")