from z3 import *
import json

# Helper function to convert minutes (from midnight) to HH:MM format
def minutes_to_timestr(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Travel times (in minutes) between locations.
# Locations: P = Presidio, G = Golden Gate Park, B = Bayview, C = Chinatown, N = North Beach, M = Mission District.
travel = {
    "P": {"G": 12, "B": 31, "C": 21, "N": 18, "M": 26},
    "G": {"P": 11, "B": 23, "C": 23, "N": 24, "M": 17},
    "B": {"P": 31, "G": 22, "C": 18, "N": 21, "M": 13},
    "C": {"P": 19, "G": 23, "B": 22, "N": 3,  "M": 18},
    "N": {"P": 17, "G": 22, "B": 22, "C": 6,  "M": 18},
    "M": {"P": 25, "G": 17, "B": 15, "C": 16, "N": 17}
}

# Starting point and starting time.
start_loc = "P"
start_time = 9 * 60  # 9:00AM in minutes from midnight (9*60 = 540)

# Define friend meeting specifications.
# Each friend is available in a specific location with a required minimum meeting duration.
# Times here are expressed in minutes from midnight.
# Note: Availability windows are given in the problem statement.
# We also require that if a friend is the first meeting, you must travel from Presidio.
# Therefore we set a lower bound as: max(availability_start, start_time + travel[start_loc][friend_location]).
friends = {
    "Daniel": {
        "location": "M",         # Mission District
        "min_duration": 105,
        "avail_start": max(7 * 60, start_time + travel["P"]["M"]),   # max(420, 540+26=566) = 566
        "avail_end": 11 * 60 + 15  # 11:15AM = 675
    },
    "Ronald": {
        "location": "C",         # Chinatown
        "min_duration": 90,
        "avail_start": max(7 * 60 + 15, start_time + travel["P"]["C"]),   # max(435, 540+21=561)=561
        "avail_end": 14 * 60 + 45  # 14:45 = 885
    },
    "Jessica": {
        "location": "G",         # Golden Gate Park
        "min_duration": 30,
        "avail_start": max(13 * 60 + 45, start_time + travel["P"]["G"]),  # max(825, 540+12=552)=825
        "avail_end": 15 * 60       # 15:00 = 900
    },
    "Ashley": {
        "location": "B",         # Bayview
        "min_duration": 105,
        "avail_start": max(17 * 60 + 15, start_time + travel["P"]["B"]),  # max(1035, 540+31=571)=1035
        "avail_end": 20 * 60       # 20:00 = 1200
    },
    "William": {
        "location": "N",         # North Beach
        "min_duration": 15,
        "avail_start": max(13 * 60 + 15, start_time + travel["P"]["N"]),  # max(795, 540+18=558)=795
        "avail_end": 20 * 60 + 15  # 20:15 = 1215
    }
}

# Create Z3 integer variables for start times of each meeting.
T = {}
for name in friends:
    T[name] = Int(f"T_{name}")

solver = Solver()

# Add time window constraints (meeting must happen within the friend’s available window)
# and the meeting must finish before the availability end.
for name, data in friends.items():
    duration = data["min_duration"]
    solver.add(T[name] >= data["avail_start"])
    solver.add(T[name] + duration <= data["avail_end"])

# Now add pairwise disjunctive (non-overlap with travel time) constraints.
# For any two distinct meetings, one must finish and travel to the next before that meeting starts.
friend_names = list(friends.keys())
n = len(friend_names)
for i in range(n):
    for j in range(i+1, n):
        name_i = friend_names[i]
        name_j = friend_names[j]
        dur_i = friends[name_i]["min_duration"]
        dur_j = friends[name_j]["min_duration"]
        loc_i = friends[name_i]["location"]
        loc_j = friends[name_j]["location"]
        # Two possibilities:
        # (i) Meeting i comes before meeting j:
        #      T[i] + duration_i + travel_time(loc_i -> loc_j) <= T[j]
        # (ii) Meeting j comes before meeting i:
        #      T[j] + duration_j + travel_time(loc_j -> loc_i) <= T[i]
        cond1 = T[name_i] + dur_i + travel[loc_i][loc_j] <= T[name_j]
        cond2 = T[name_j] + dur_j + travel[loc_j][loc_i] <= T[name_i]
        solver.add(Or(cond1, cond2))

# Solve the scheduling problem.
if solver.check() == sat:
    model = solver.model()
    # Build the itinerary as a list of meeting entries.
    itinerary = []
    # Create a list of (start_time, name) tuples to sort them chronologically.
    schedule = []
    for name in friend_names:
        start_val = model[T[name]].as_long()
        duration = friends[name]["min_duration"]
        finish_val = start_val + duration
        schedule.append((start_val, name, finish_val))
    schedule = sorted(schedule, key=lambda x: x[0])
    
    for start_val, name, finish_val in schedule:
        entry = {
            "action": "meet",
            "person": name,
            "start_time": minutes_to_timestr(start_val),
            "end_time": minutes_to_timestr(finish_val)
        }
        itinerary.append(entry)
    
    # Output the itinerary in JSON format.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid schedule found.")