from z3 import *
import json

# Define travel times as a dictionary
travel_dict = {
    "Alamo Square": {
        "Russian Hill": 13,
        "Presidio": 18,
        "Chinatown": 16,
        "Sunset District": 16,
        "The Castro": 8,
        "Embarcadero": 17,
        "Golden Gate Park": 9
    },
    "Russian Hill": {
        "Alamo Square": 15,
        "Presidio": 14,
        "Chinatown": 9,
        "Sunset District": 23,
        "The Castro": 21,
        "Embarcadero": 8,
        "Golden Gate Park": 21
    },
    "Presidio": {
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Chinatown": 21,
        "Sunset District": 15,
        "The Castro": 21,
        "Embarcadero": 20,
        "Golden Gate Park": 12
    },
    "Chinatown": {
        "Alamo Square": 17,
        "Russian Hill": 7,
        "Presidio": 19,
        "Sunset District": 29,
        "The Castro": 22,
        "Embarcadero": 5,
        "Golden Gate Park": 23
    },
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Presidio": 16,
        "Chinatown": 30,
        "The Castro": 17,
        "Embarcadero": 31,
        "Golden Gate Park": 11
    },
    "The Castro": {
        "Alamo Square": 8,
        "Russian Hill": 18,
        "Presidio": 20,
        "Chinatown": 20,
        "Sunset District": 17,
        "Embarcadero": 22,
        "Golden Gate Park": 11
    },
    "Embarcadero": {
        "Alamo Square": 19,
        "Russian Hill": 8,
        "Presidio": 20,
        "Chinatown": 7,
        "Sunset District": 30,
        "The Castro": 25,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Presidio": 11,
        "Chinatown": 23,
        "Sunset District": 10,
        "The Castro": 13,
        "Embarcadero": 25
    }
}

# Define friends with their constraints (times in minutes from midnight)
friends = [
    {"name": "Emily", "location": "Russian Hill", "avail_start": 12*60+15, "avail_end": 14*60+15, "min_dur": 105},
    {"name": "Mark", "location": "Presidio", "avail_start": 14*60+45, "avail_end": 19*60+30, "min_dur": 60},
    {"name": "Deborah", "location": "Chinatown", "avail_start": 7*60+30, "avail_end": 15*60+30, "min_dur": 45},
    {"name": "Margaret", "location": "Sunset District", "avail_start": 21*60+30, "avail_end": 22*60+30, "min_dur": 60},
    {"name": "George", "location": "The Castro", "avail_start": 7*60+30, "avail_end": 14*60+15, "min_dur": 60},
    {"name": "Andrew", "location": "Embarcadero", "avail_start": 20*60+15, "avail_end": 22*60, "min_dur": 75},
    {"name": "Steven", "location": "Golden Gate Park", "avail_start": 11*60+15, "avail_end": 21*60+15, "min_dur": 105}
]

# Initialize Z3 optimizer
opt = Optimize()

# Create variables for each friend
meet_vars = []
start_vars = []
end_vars = []
locations = []

for idx, friend in enumerate(friends):
    meet_var = Bool(f"meet_{friend['name']}")
    start_var = Int(f"start_{friend['name']}")
    end_var = Int(f"end_{friend['name']}")
    meet_vars.append(meet_var)
    start_vars.append(start_var)
    end_vars.append(end_var)
    locations.append(friend['location'])

    # If meeting this friend, enforce constraints
    opt.add(Implies(meet_var, start_var >= friend['avail_start']))
    opt.add(Implies(meet_var, end_var <= friend['avail_end']))
    opt.add(Implies(meet_var, end_var == start_var + friend['min_dur']))
    # Travel time from Alamo Square to this friend's location
    travel_time = travel_dict["Alamo Square"][friend['location']]
    opt.add(Implies(meet_var, start_var >= 9*60 + travel_time))

# Add disjunctive constraints for every pair of distinct friends
n = len(friends)
for i in range(n):
    for j in range(i + 1, n):
        # If both meetings are scheduled, then enforce disjunctive constraint
        both_meet = And(meet_vars[i], meet_vars[j])
        loc_i = locations[i]
        loc_j = locations[j]
        travel_ij = travel_dict[loc_i][loc_j]
        travel_ji = travel_dict[loc_j][loc_i]
        constraint = Or(
            end_vars[i] + travel_ij <= start_vars[j],
            end_vars[j] + travel_ji <= start_vars[i]
        )
        opt.add(Implies(both_meet, constraint))

# Maximize the number of meetings
obj = Sum([If(var, 1, 0) for var in meet_vars])
opt.maximize(obj)

# Check satisfiability
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for i, friend in enumerate(friends):
        if is_true(model[meet_vars[i]]):
            start_val = model.eval(start_vars[i]).as_long()
            end_val = model.eval(end_vars[i]).as_long()
            start_hour = start_val // 60
            start_minute = start_val % 60
            end_hour = end_val // 60
            end_minute = end_val % 60
            start_time = f"{start_hour:02d}:{start_minute:02d}"
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")