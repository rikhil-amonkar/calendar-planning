import json
from z3 import *

# Travel times in minutes
travel_times = {
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Financial District"): 19,
    
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Financial District"): 23,
    
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Presidio"): 22
}

def get_travel_time(fr, to):
    return travel_times[(fr, to)]

# Friend meeting definitions
# Times are in minutes from midnight.
# Embarcadero arrival is at 9:00 -> 540 minutes.
# Mary is available 8:45 (525) to 11:45 (705), minimum 45 min.
# Kevin is available 10:15 (615) to 16:15 (975), minimum 90 min.
# Deborah is available 15:00 (900) to 19:15 (1155), minimum 120 min.
# Stephanie is available 10:00 (600) to 17:15 (1035), minimum 120 min.
# Emily is available 11:30 (690) to 21:45 (1305), minimum 105 min.
friends = [
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "avail_start": 525,
        "avail_end": 705,
        "min_duration": 45
    },
    {
        "name": "Kevin",
        "location": "Haight-Ashbury",
        "avail_start": 615,
        "avail_end": 975,
        "min_duration": 90
    },
    {
        "name": "Deborah",
        "location": "Bayview",
        "avail_start": 900,
        "avail_end": 1155,
        "min_duration": 120
    },
    {
        "name": "Stephanie",
        "location": "Presidio",
        "avail_start": 600,
        "avail_end": 1035,
        "min_duration": 120
    },
    {
        "name": "Emily",
        "location": "Financial District",
        "avail_start": 690,
        "avail_end": 1305,
        "min_duration": 105
    }
]

n_friends = len(friends)
opt = Optimize()

# Create decision variables for each meeting:
# x: whether friend is met, s: start time of meeting, pos: order position in the itinerary.
x_vars = [Bool(f"x_{i}") for i in range(n_friends)]
s_vars = [Int(f"s_{i}") for i in range(n_friends)]
pos_vars = [Int(f"pos_{i}") for i in range(n_friends)]

# Constraints for each friend meeting
for i, friend in enumerate(friends):
    # If meeting is scheduled, start time must be within the friend's available window.
    opt.add(Implies(x_vars[i], s_vars[i] >= friend["avail_start"]))
    opt.add(Implies(x_vars[i], s_vars[i] + friend["min_duration"] <= friend["avail_end"]))
    # If meeting is scheduled, its order position must be between 0 and n_friends-1.
    opt.add(Implies(x_vars[i], And(pos_vars[i] >= 0, pos_vars[i] < n_friends)))
    # If this meeting is the first one (position 0), ensure travel from Embarcadero is accounted for.
    travel_from_origin = get_travel_time("Embarcadero", friend["location"])
    opt.add(Implies(And(x_vars[i], pos_vars[i] == 0), s_vars[i] >= 540 + travel_from_origin))

# Ordering constraints between any two scheduled meetings
for i in range(n_friends):
    for j in range(i+1, n_friends):
        # If both meetings are scheduled, their order positions must be different.
        opt.add(Implies(And(x_vars[i], x_vars[j]), pos_vars[i] != pos_vars[j]))
        # Define travel times and durations.
        t_ij = get_travel_time(friends[i]["location"], friends[j]["location"])
        t_ji = get_travel_time(friends[j]["location"], friends[i]["location"])
        d_i = friends[i]["min_duration"]
        d_j = friends[j]["min_duration"]
        # If both meetings are scheduled, then one must come before the other.
        # If friend i is before friend j, then s_i + d_i + travel(i->j) <= s_j.
        # Else, if friend j is before friend i, then s_j + d_j + travel(j->i) <= s_i.
        opt.add(Implies(And(x_vars[i], x_vars[j]),
                        Or(
                            And(pos_vars[i] < pos_vars[j], s_vars[i] + d_i + t_ij <= s_vars[j]),
                            And(pos_vars[j] < pos_vars[i], s_vars[j] + d_j + t_ji <= s_vars[i])
                        )
                       )
               )

# Ensure that if any meeting is scheduled, exactly one meeting is the first (pos == 0)
first_meeting_count = Sum([If(And(x_vars[i], pos_vars[i] == 0), 1, 0) for i in range(n_friends)])
total_scheduled = Sum([If(x_vars[i], 1, 0) for i in range(n_friends)])
opt.add(Or(total_scheduled == 0, first_meeting_count == 1))

# Objective: maximize the total number of meetings scheduled.
opt.maximize(total_scheduled)

# Solve the SMT optimization
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    for i, friend in enumerate(friends):
        if is_true(model.evaluate(x_vars[i])):
            start_time = model.evaluate(s_vars[i]).as_long()
            end_time = start_time + friend["min_duration"]
            pos_val = model.evaluate(pos_vars[i]).as_long()
            scheduled.append((pos_val, friend, start_time, end_time))
    # Sort meetings by their position in the itinerary.
    scheduled.sort(key=lambda item: item[0])
    
    def format_time(minutes):
        hr = minutes // 60
        mn = minutes % 60
        return f"{hr}:{mn:02d}"
    
    itinerary = []
    for order, friend, start, end in scheduled:
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))