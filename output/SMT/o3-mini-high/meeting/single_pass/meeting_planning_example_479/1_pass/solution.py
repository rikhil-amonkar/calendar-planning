from z3 import *
import json

# Helper function to convert minutes (from midnight) to HH:MM 24-hour format.
def minutes_to_str(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

# Define the meeting requirements (in minutes) for each friend.
meeting_durations = {
    "Mary": 45,
    "Kevin": 90,
    "Stephanie": 120,
    "Emily": 105,
    "Deborah": 120,
}

# Define the availability windows (start, end) in minutes-from-midnight.
# Mary: 8:45 - 11:45, Kevin: 10:15 - 16:15, Stephanie: 10:00 - 17:15,
# Emily: 11:30 - 21:45, Deborah: 15:00 - 19:15.
availability = {
    "Mary": (8*60 + 45, 11*60 + 45),          # 525 to 705
    "Kevin": (10*60 + 15, 16*60 + 15),         # 615 to 975
    "Stephanie": (10*60, 17*60 + 15),          # 600 to 1035
    "Emily": (11*60 + 30, 21*60 + 45),         # 690 to 1305
    "Deborah": (15*60, 19*60 + 15),            # 900 to 1155
}

# Each friend is met at a specific location:
locations = {
    "Mary": "Golden Gate Park",
    "Kevin": "Haight-Ashbury",
    "Stephanie": "Presidio",
    "Emily": "Financial District",
    "Deborah": "Bayview"
}

# Given travel times (in minutes) between all locations:
travel_times = {
    # From Embarcadero to friends' locations:
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    
    # Between the places:
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
    ("Presidio", "Financial District"): 22,
    
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Presidio"): 22,
}

# A function to retrieve travel time between two friends' meeting locations.
def travel_time_between(friend1, friend2):
    loc1 = locations[friend1]
    loc2 = locations[friend2]
    return travel_times[(loc1, loc2)]

# List of friends to schedule meetings with.
friends = ["Mary", "Kevin", "Stephanie", "Emily", "Deborah"]

# Create Z3 integer variables for:
#  - s[friend]: the meeting start time (in minutes from midnight)
#  - order[friend]: the order (position in our schedule, 1 = first, etc.)
s = {}
order = {}
for friend in friends:
    s[friend] = Int(f"s_{friend}")
    order[friend] = Int(f"order_{friend}")

solver = Solver()

# Constraint: Each meeting must occur during the friend’s availability.
for friend in friends:
    a_start, a_end = availability[friend]
    duration = meeting_durations[friend]
    solver.add(s[friend] >= a_start)
    solver.add(s[friend] + duration <= a_end)
    # Order value between 1 and the total number of meetings.
    solver.add(order[friend] >= 1, order[friend] <= len(friends))

# You arrive at Embarcadero at 09:00 (i.e. 540 minutes).
# For the very first meeting in your schedule, you must travel from Embarcadero.
for friend in friends:
    travel_from_start = travel_times[("Embarcadero", locations[friend])]
    required_arrival = 540 + travel_from_start
    # If this friend is scheduled first then their meeting cannot start before the travel time.
    solver.add(Implies(order[friend] == 1, s[friend] >= required_arrival))

# The order in which meetings occur must be a permutation.
solver.add(Distinct([order[f] for f in friends]))

# If friend f1 is scheduled before friend f2 then you must finish f1's meeting and travel,
# arriving at f2’s location by the f2 meeting start time.
for f1 in friends:
    for f2 in friends:
        if f1 == f2:
            continue
        duration = meeting_durations[f1]
        travel_dur = travel_time_between(f1, f2)
        solver.add(Implies(order[f1] < order[f2],
                           s[f1] + duration + travel_dur <= s[f2]))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    schedule = []
    # Gather the model values and sort by meeting order.
    for friend in friends:
        start_time_val = model[s[friend]].as_long()
        finish_time_val = start_time_val + meeting_durations[friend]
        schedule.append((model[order[friend]].as_long(), friend, start_time_val, finish_time_val))
    schedule.sort(key=lambda tup: tup[0])  # sort by order

    itinerary = []
    for order_val, friend, start, finish in schedule:
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(finish)
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))
else:
    print("No solution found")