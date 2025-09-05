from z3 import Int, Bool, Optimize, If, And, Or, Implies, Not, sat
import json

# Define travel times as given in minutes (non-symmetric values provided)
travel = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Union Square"): 22,
}

# Define friend meeting details
# Each friend is associated with a fixed location, an availability window and a minimum meeting duration.
friends = ["Karen", "Jessica", "Matthew", "Michelle", "Carol", "Stephanie", "Linda"]
locations = ["Russian Hill", "The Castro", "Richmond District", "Marina District", "North Beach", "Union Square", "Golden Gate Park"]

# Availability times in minutes from midnight
# Karen: 20:45 - 21:45 => 1245 to 1305
# Jessica: 15:45 - 19:30 => 945 to 1170
# Matthew: 7:30 - 15:15 => 450 to 915
# Michelle: 10:30 - 18:45 => 630 to 1125
# Carol: 12:00 - 17:00 => 720 to 1020
# Stephanie: 10:45 - 14:15 => 645 to 855
# Linda: 10:45 - 22:00 => 645 to 1320
avail_starts = [1245, 945, 450, 630, 720, 645, 645]
avail_ends   = [1305, 1170, 915, 1125, 1020, 855, 1320]
min_durations = [60, 60, 15, 75, 90, 30, 90]

# Arrival information: You arrive at Sunset District at 9:00am (9*60 = 540 minutes)
start_time_sunset = 540

num_friends = len(friends)

# Create Z3 variables for each friend meeting:
# s[i] and e[i] are the meeting start and end times (in minutes from midnight)
# order[i] is an integer representing the order in the itinerary. 0 means not scheduled.
# selected[i] is a Boolean indicating whether you meet friend i.
s_vars = [Int(f"s_{i}") for i in range(num_friends)]
e_vars = [Int(f"e_{i}") for i in range(num_friends)]
order_vars = [Int(f"order_{i}") for i in range(num_friends)]
selected = [Bool(f"selected_{i}") for i in range(num_friends)]

opt = Optimize()

# Add domain constraints and meeting window constraints for each friend
for i in range(num_friends):
    # If the meeting is selected then order must be > 0; if not, order equals 0.
    opt.add(Or(And(selected[i], order_vars[i] > 0), And(Not(selected[i]), order_vars[i] == 0)))
    # Domain for order: if selected, order between 1 and num_friends.
    opt.add(order_vars[i] >= 0, order_vars[i] <= num_friends)
    
    # If meeting is selected, then meeting start and end must respect the friend's availability and duration.
    opt.add(Implies(selected[i],
                      And(s_vars[i] >= avail_starts[i],
                          e_vars[i] <= avail_ends[i],
                          e_vars[i] - s_vars[i] >= min_durations[i])))
    # Also, meeting start/end should be non-negative and within the day.
    opt.add(s_vars[i] >= 0, e_vars[i] >= 0, e_vars[i] <= 1440)

# Add ordering constraints: For any two meetings that are selected, they must not overlap considering travel times.
for i in range(num_friends):
    for j in range(num_friends):
        if i != j:
            # If both meetings are selected and i comes before j then
            # meeting j must start after meeting i ends plus travel time from i's location to j's location.
            if (locations[i], locations[j]) in travel:
                travel_time_ij = travel[(locations[i], locations[j])]
            else:
                # if not defined, use a large travel time (should not occur)
                travel_time_ij = 1000
            opt.add(Implies(And(selected[i], selected[j], order_vars[i] < order_vars[j]),
                            s_vars[j] >= e_vars[i] + travel_time_ij))

# For the first meeting in the schedule (order == 1), you must travel from Sunset District first.
for i in range(num_friends):
    if ( "Sunset District", locations[i] ) in travel:
        travel_from_sunset = travel[("Sunset District", locations[i])]
    else:
        travel_from_sunset = 1000
    opt.add(Implies(And(selected[i], order_vars[i] == 1),
                    s_vars[i] >= start_time_sunset + travel_from_sunset))

# Ensure that if two meetings are selected they have distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Implies(And(selected[i], selected[j]), order_vars[i] != order_vars[j]))

# Objective: maximize the number of meetings (selected friends)
objective = sum([If(selected[i], 1, 0) for i in range(num_friends)])
opt.maximize(objective)

# Check the model
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    
    # Gather meeting info for selected meetings
    meetings = []
    for i in range(num_friends):
        if model.evaluate(selected[i]):
            order_val = model.evaluate(order_vars[i]).as_long()
            start_val = model.evaluate(s_vars[i]).as_long()
            end_val = model.evaluate(e_vars[i]).as_long()
            meetings.append((order_val, friends[i], locations[i], start_val, end_val))
    
    # Sort meetings by order (ascending)
    meetings.sort(key=lambda x: x[0])
    
    # Function to format time in H:MM (24-hour, no leading zero in hour)
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"
    
    for order_val, person, location, start_val, end_val in meetings:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(start_val),
            "end_time": format_time(end_val)
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))