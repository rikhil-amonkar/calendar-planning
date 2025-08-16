from z3 import *
import json

# Helper function: convert minutes since midnight to HH:MM format
def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Data for friends: name, location, availability (start, end) in minutes from midnight, minimum meeting duration.
# Times: 9:00 AM = 540, 7:30 AM = 450, 12:15 PM = 735, 2:15 PM = 855, 2:45 PM = 885, 7:30 PM = 1170,
# 7:30 AM = 450, 3:30 PM = 930, 11:15 AM = 675, 9:15 PM = 1275, 8:15 PM = 1215, 10:00 PM = 1320,
# 9:30 PM = 1290, 10:30 PM = 1350.
names = ["Emily", "Mark", "Deborah", "Margaret", "George", "Andrew", "Steven"]
locations = ["Russian Hill", "Presidio", "Chinatown", "Sunset District", "The Castro", "Embarcadero", "Golden Gate Park"]
availabilities = [
    (735, 855, 105),   # Emily: 12:15 - 14:15, 105 min
    (885, 1170, 60),   # Mark: 14:45 - 19:30, 60 min
    (450, 930, 45),    # Deborah: 7:30 - 15:30, 45 min
    (1290, 1350, 60),  # Margaret: 21:30 - 22:30, 60 min
    (450, 855, 60),    # George: 7:30 - 14:15, 60 min
    (1215, 1320, 75),  # Andrew: 20:15 - 22:00, 75 min
    (675, 1275, 105)   # Steven: 11:15 - 21:15, 105 min
]

# Travel times in minutes between locations (note: times are not necessarily symmetric)
travel_times = {
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,

    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Golden Gate Park"): 21,

    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,

    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,

    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Embarcadero"): 31,
    ("Sunset District", "Golden Gate Park"): 11,

    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,

    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,

    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
}

n = len(names)

# Create an Optimize() instance (for optimization over which meetings to schedule)
opt = Optimize()

# Decision variables for each friend:
# s[i]: start time of meeting (minutes since midnight)
# e[i]: end time of meeting
# order[i]: the position in the schedule (if scheduled, a value 1..n, else 0)
# meet[i]: Boolean flag; True if we decide to meet friend i.
s_vars = [Int(f"s_{i}") for i in range(n)]
e_vars = [Int(f"e_{i}") for i in range(n)]
order_vars = [Int(f"order_{i}") for i in range(n)]
meet_vars = [Bool(f"meet_{i}") for i in range(n)]

# Add constraints for each friend based on availability and meeting duration.
for i in range(n):
    avail_start, avail_end, duration = availabilities[i]
    # If we decide to meet the friend, then meeting start and end must lie in the availability window
    # and the meeting must last at least the required duration.
    opt.add(If(meet_vars[i],
               And(s_vars[i] >= avail_start,
                   e_vars[i] <= avail_end,
                   e_vars[i] - s_vars[i] >= duration),
               And(s_vars[i] == 0, e_vars[i] == 0)))
    # If meeting is scheduled, assign an order between 1 and n, else order is 0.
    opt.add(If(meet_vars[i],
               And(order_vars[i] >= 1, order_vars[i] <= n),
               order_vars[i] == 0))

# Since the windows for Margaret (index 3) and Andrew (index 5) overlap insufficiently,
# we cannot meet them both. So force at most one of them to be scheduled.
opt.add(Not(And(meet_vars[3], meet_vars[5])))

# Ensure that scheduled meetings receive distinct order numbers.
for i in range(n):
    for j in range(i+1, n):
        opt.add(Implies(And(meet_vars[i], meet_vars[j]), order_vars[i] != order_vars[j]))

# Travel constraints for consecutive meetings in the schedule.
# For any two different meetings i and j, if both are scheduled and j immediately follows i,
# then the start time of meeting j must be at least the end time of meeting i plus the travel time
# from friend i's location to friend j's location.
for i in range(n):
    for j in range(n):
        if i != j:
            tt = travel_times[(locations[i], locations[j])]
            opt.add(Implies(And(meet_vars[i],
                                meet_vars[j],
                                order_vars[j] == order_vars[i] + 1),
                            s_vars[j] >= e_vars[i] + tt))

# For the first scheduled meeting, the travel time has to be computed from the starting point: Alamo Square.
for i in range(n):
    tt = travel_times[("Alamo Square", locations[i])]
    opt.add(Implies(And(meet_vars[i], order_vars[i] == 1),
                    s_vars[i] >= 540 + tt))  # 9:00 AM -> 540 minutes

# Our objective is to maximize the number of meetings (i.e. friends met)
opt.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(n)]))

# Check for a solution.
if opt.check() == sat:
    mod = opt.model()
    # Collect scheduled meetings (those with meet_vars[i] True) along with their order.
    scheduled = []
    for i in range(n):
        if is_true(mod.evaluate(meet_vars[i])):
            scheduled.append((mod.evaluate(order_vars[i]).as_long(), i))
    # Sort the meetings by their order in the schedule.
    scheduled.sort(key=lambda x: x[0])
    
    itinerary = []
    for order_num, i in scheduled:
        start_time = mod.evaluate(s_vars[i]).as_long()
        end_time = mod.evaluate(e_vars[i]).as_long()
        itinerary.append({"action": "meet",
                          "person": names[i],
                          "start_time": minutes_to_str(start_time),
                          "end_time": minutes_to_str(end_time)})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")