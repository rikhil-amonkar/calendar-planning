from z3 import *
import json

# Define travel time functions using Z3 If-then-else expressions

def travel_time_from_start(p):
    # From Golden Gate Park to each location (friend index):
    # 0: Fisherman's Wharf -> 24
    # 1: Bayview -> 23
    # 2: Mission District -> 17
    # 3: Embarcadero -> 25
    # 4: Financial District -> 26
    return If(p == 0, 24,
           If(p == 1, 23,
           If(p == 2, 17,
           If(p == 3, 25,
           If(p == 4, 26, 0)))))

def get_travel_time(prev, curr):
    # Travel times between locations based on friend indices:
    # Mapping friend index to location:
    # 0: Fisherman's Wharf, 1: Bayview, 2: Mission District, 3: Embarcadero, 4: Financial District
    return If(prev == 0,
             If(curr == 0, 0,
             If(curr == 1, 26,
             If(curr == 2, 22,
             If(curr == 3, 8,
             If(curr == 4, 11, 0))))),
           If(prev == 1,
             If(curr == 0, 25,
             If(curr == 1, 0,
             If(curr == 2, 13,
             If(curr == 3, 19,
             If(curr == 4, 19, 0)))),
           If(prev == 2,
             If(curr == 0, 22,
             If(curr == 1, 15,
             If(curr == 2, 0,
             If(curr == 3, 19,
             If(curr == 4, 17, 0)))),
           If(prev == 3,
             If(curr == 0, 6,
             If(curr == 1, 21,
             If(curr == 2, 20,
             If(curr == 3, 0,
             If(curr == 4, 5, 0)))),
           If(prev == 4,
             If(curr == 0, 10,
             If(curr == 1, 19,
             If(curr == 2, 17,
             If(curr == 3, 4,
             If(curr == 4, 0, 0)))),
             0)))))))
    
# Friend data: each friend has a fixed location, availability window (in minutes after midnight), and minimum meeting duration.
# Times: 9:00 is 540, 8:00 is 480, 5:30 is 1050, 11:15 is 675, 3:15 is 915, etc.
friend_data = [
    {"name": "Joseph", "location": "Fisherman's Wharf", "avail_start": 480, "avail_end": 1050, "min_dur": 90},
    {"name": "Jeffrey", "location": "Bayview", "avail_start": 1050, "avail_end": 1290, "min_dur": 60},
    {"name": "Kevin", "location": "Mission District", "avail_start": 675, "avail_end": 915, "min_dur": 30},
    {"name": "David", "location": "Embarcadero", "avail_start": 495, "avail_end": 540, "min_dur": 30},
    {"name": "Barbara", "location": "Financial District", "avail_start": 630, "avail_end": 990, "min_dur": 15}
]

# Extract individual parameters for ease of use
avail_start = [f["avail_start"] for f in friend_data]
avail_end   = [f["avail_end"]   for f in friend_data]
min_dur     = [f["min_dur"]     for f in friend_data]
names       = [f["name"]        for f in friend_data]
locations   = [f["location"]    for f in friend_data]

# We allow up to 5 meeting slots (one per friend)
num_slots = 5

# Create Z3 optimizer
opt = Optimize()

# Decision variables for each slot:
# used[r] indicates whether slot r is used.
# person[r] is an integer in [0,4] indicating which friend is met in slot r.
# start_time[r] and end_time[r] are the start and end times (in minutes) for that meeting.
used = [Bool(f"used_{r}") for r in range(num_slots)]
person = [Int(f"person_{r}") for r in range(num_slots)]
start_time = [Int(f"start_{r}") for r in range(num_slots)]
end_time = [Int(f"end_{r}") for r in range(num_slots)]

# Domain constraints and friend availability constraints for each slot
for r in range(num_slots):
    # person must be between 0 and 4 (if the slot is used)
    opt.add(person[r] >= 0, person[r] <= 4)
    # If slot r is used, then meeting times must satisfy the availability and minimum duration for the chosen friend
    opt.add(Implies(used[r],
        And(
            # For friend 0 (Joseph) constraints
            If(person[r] == 0, start_time[r] >= avail_start[0], True),
            If(person[r] == 0, end_time[r] <= avail_end[0], True),
            If(person[r] == 0, end_time[r] - start_time[r] >= min_dur[0], True),
            # For friend 1 (Jeffrey)
            If(person[r] == 1, start_time[r] >= avail_start[1], True),
            If(person[r] == 1, end_time[r] <= avail_end[1], True),
            If(person[r] == 1, end_time[r] - start_time[r] >= min_dur[1], True),
            # For friend 2 (Kevin)
            If(person[r] == 2, start_time[r] >= avail_start[2], True),
            If(person[r] == 2, end_time[r] <= avail_end[2], True),
            If(person[r] == 2, end_time[r] - start_time[r] >= min_dur[2], True),
            # For friend 3 (David)
            If(person[r] == 3, start_time[r] >= avail_start[3], True),
            If(person[r] == 3, end_time[r] <= avail_end[3], True),
            If(person[r] == 3, end_time[r] - start_time[r] >= min_dur[3], True),
            # For friend 4 (Barbara)
            If(person[r] == 4, start_time[r] >= avail_start[4], True),
            If(person[r] == 4, end_time[r] <= avail_end[4], True),
            If(person[r] == 4, end_time[r] - start_time[r] >= min_dur[4], True)
        )
    ))
    
    # Ensure that if a slot is used, the meeting duration is non-negative.
    opt.add(Implies(used[r], end_time[r] >= start_time[r]))

# Constraint for the first meeting: leave from Golden Gate Park at 9:00 (540 minutes)
opt.add(Implies(used[0],
    start_time[0] >= 540 + travel_time_from_start(person[0])
))

# For subsequent meetings, account for travel time from the previous meeting's location.
for r in range(1, num_slots):
    opt.add(Implies(used[r],
        start_time[r] >= end_time[r-1] + get_travel_time(person[r-1], person[r])
    ))
    # Enforce that if slot r is used, then the previous slot must also be used.
    opt.add(Implies(used[r], used[r-1]))

# Each friend can only be met once: uniqueness across used slots.
for i in range(num_slots):
    for j in range(i+1, num_slots):
        opt.add(Implies(And(used[i], used[j]), person[i] != person[j]))

# Objective: maximize the number of meetings (slots used)
num_meetings = Sum([If(used[r], 1, 0) for r in range(num_slots)])
opt.maximize(num_meetings)

# Check for an optimal solution
if opt.check() == sat:
    m = opt.model()
    
    # Helper function to format time (minutes since midnight) into "H:MM" format.
    def format_time(t):
        hour = t // 60
        minute = t % 60
        return f"{hour}:{minute:02d}"
    
    itinerary = []
    # Process each slot in order
    for r in range(num_slots):
        if m.eval(used[r]):
            p = m.eval(person[r]).as_long()
            st = m.eval(start_time[r]).as_long()
            et = m.eval(end_time[r]).as_long()
            meeting = {
                "action": "meet",
                "location": locations[p],
                "person": names[p],
                "start_time": format_time(st),
                "end_time": format_time(et)
            }
            itinerary.append(meeting)
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))