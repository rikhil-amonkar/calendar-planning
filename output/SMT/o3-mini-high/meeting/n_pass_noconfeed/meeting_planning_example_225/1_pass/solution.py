from z3 import *
import json

# Define friend IDs and their properties
# 0 means no meeting scheduled in that slot.
# Friend 1: Sarah, location: North Beach, available [960, 1095] (16:00 to 18:15), meeting duration >= 60 minutes.
# Friend 2: Jeffrey, location: Union Square, available [900, 1320] (15:00 to 22:00), meeting duration >= 75 minutes.
# Friend 3: Brian, location: Alamo Square, available [960, 1050] (16:00 to 17:30), meeting duration >= 75 minutes.

# Travel times (in minutes) between locations:
# From Sunset District to:
#   North Beach: 29, Union Square: 30, Alamo Square: 17.
# Between friends' locations:
#   North Beach -> Union Square: 7
#   North Beach -> Alamo Square: 16
#   Union Square -> North Beach: 10
#   Union Square -> Alamo Square: 15
#   Alamo Square -> North Beach: 15
#   Alamo Square -> Union Square: 14

# Helper function: travel time between two friend locations given friend IDs (assumes value in {1,2,3})
def travel_time_expr(a, b):
    return If(And(a == 1, b == 2), 7,
           If(And(a == 1, b == 3), 16,
           If(And(a == 2, b == 1), 10,
           If(And(a == 2, b == 3), 15,
           If(And(a == 3, b == 1), 15,
           If(And(a == 3, b == 2), 14, 0))))))

# Convert minutes (from midnight) to H:MM string (24-hour, no leading zero for hour)
def format_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Create an Optimize object to maximize scheduled meetings count
opt = Optimize()

# Slot decision variables: s1, s2, s3 indicate which friend is scheduled in each slot (0 if none)
s1 = Int('s1')
s2 = Int('s2')
s3 = Int('s3')
opt.add(And(s1 >= 0, s1 <= 3))
opt.add(And(s2 >= 0, s2 <= 3))
opt.add(And(s3 >= 0, s3 <= 3))

# Contiguity: if a later slot is scheduled then the previous one must be scheduled.
opt.add(Implies(s2 != 0, s1 != 0))
opt.add(Implies(s3 != 0, s2 != 0))

# Uniqueness: if slots are non-zero, they must be different.
opt.add(Implies(And(s1 != 0, s2 != 0), s1 != s2))
opt.add(Implies(And(s1 != 0, s3 != 0), s1 != s3))
opt.add(Implies(And(s2 != 0, s3 != 0), s2 != s3))

# For each slot, define meeting start and end times (in minutes from midnight)
S1 = Int('S1')
E1 = Int('E1')
S2 = Int('S2')
E2 = Int('E2')
S3 = Int('S3')
E3 = Int('E3')

# For slots with no meeting, force start and end to be 0.
opt.add(Implies(s1 == 0, And(S1 == 0, E1 == 0)))
opt.add(Implies(s2 == 0, And(S2 == 0, E2 == 0)))
opt.add(Implies(s3 == 0, And(S3 == 0, E3 == 0)))

# For scheduled slots, add availability and duration constraints based on friend
# Slot 1 constraints:
# Also, must depart from Sunset District (arrival at 9:00 = 540 minutes) plus travel time.
opt.add(Implies(s1 != 0,
    S1 >= 540 + If(s1 == 1, 29, If(s1 == 2, 30, If(s1 == 3, 17, 0)))
))

opt.add(Implies(s1 == 1, And(S1 >= 960, E1 <= 1095, E1 - S1 >= 60)))
opt.add(Implies(s1 == 2, And(S1 >= 900, E1 <= 1320, E1 - S1 >= 75)))
opt.add(Implies(s1 == 3, And(S1 >= 960, E1 <= 1050, E1 - S1 >= 75)))

# Slot 2 constraints:
opt.add(Implies(s2 == 1, And(S2 >= 960, E2 <= 1095, E2 - S2 >= 60)))
opt.add(Implies(s2 == 2, And(S2 >= 900, E2 <= 1320, E2 - S2 >= 75)))
opt.add(Implies(s2 == 3, And(S2 >= 960, E2 <= 1050, E2 - S2 >= 75)))
# Ordering: if slot1 and slot2 are scheduled, slot2's meeting must start after slot1 ends plus travel time (from s1's location to s2's location)
opt.add(Implies(And(s1 != 0, s2 != 0), S2 >= E1 + travel_time_expr(s1, s2)))

# Slot 3 constraints:
opt.add(Implies(s3 == 1, And(S3 >= 960, E3 <= 1095, E3 - S3 >= 60)))
opt.add(Implies(s3 == 2, And(S3 >= 900, E3 <= 1320, E3 - S3 >= 75)))
opt.add(Implies(s3 == 3, And(S3 >= 960, E3 <= 1050, E3 - S3 >= 75)))
# Ordering: if slot2 and slot3 are scheduled, slot3's meeting must start after slot2 ends plus travel time
opt.add(Implies(And(s2 != 0, s3 != 0), S3 >= E2 + travel_time_expr(s2, s3)))

# Define objective: maximize the total number of meetings scheduled.
meeting_count = If(s1 != 0, 1, 0) + If(s2 != 0, 1, 0) + If(s3 != 0, 1, 0)
h = opt.maximize(meeting_count)

# Check for optimal solution
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    # Mapping friend id to (name, location)
    friend_map = {
        1: ("Sarah", "North Beach"),
        2: ("Jeffrey", "Union Square"),
        3: ("Brian", "Alamo Square")
    }
    
    # For each slot in order, if scheduled (s != 0), add to itinerary.
    slots = [(s1, S1, E1), (s2, S2, E2), (s3, S3, E3)]
    for idx, (slot, start_var, end_var) in enumerate(slots, start=1):
        # Evaluate the friend id value
        friend_id = m.eval(slot).as_long()
        if friend_id != 0:
            # Get meeting start and end times
            start_time = m.eval(start_var).as_long()
            end_time = m.eval(end_var).as_long()
            # Format times as H:MM
            start_str = format_time(start_time)
            end_str = format_time(end_time)
            person, location = friend_map[friend_id]
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": start_str,
                "end_time": end_str
            })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    result = {"itinerary": []}
    print(json.dumps(result, indent=2))