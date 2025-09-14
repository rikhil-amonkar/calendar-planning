from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

# Create an Optimize instance
opt = Optimize()

# Define variables for meeting start and end times (minutes from midnight)
S_R = Int('S_R')  # Rebecca start
E_R = Int('E_R')  # Rebecca end
S_K = Int('S_K')  # Karen start
E_K = Int('E_K')  # Karen end
S_C = Int('S_C')  # Carol start
E_C = Int('E_C')  # Carol end

# Ordering variables (each meeting gets an order 1,2,3)
order_R = Int('order_R')
order_K = Int('order_K')
order_C = Int('order_C')

# A variable for the finish time of the last meeting (to minimize overall finish time)
finish_time = Int('finish_time')

# Define constant times in minutes from midnight
arrival = 9 * 60  # 9:00 AM -> 540

# Availabilities and minimum meeting durations
avail_R_start = 11 * 60 + 30  # Rebecca: 11:30 AM -> 690
avail_R_end   = 20 * 60 + 15  # Rebecca: 8:15 PM -> 1215
avail_K_start = 12 * 60 + 45  # Karen: 12:45 PM -> 765
avail_K_end   = 15 * 60       # Karen: 15:00 -> 900
avail_C_start = 10 * 60 + 15  # Carol: 10:15 AM -> 615
avail_C_end   = 11 * 60 + 45  # Carol: 11:45 AM -> 705

min_R = 120
min_K = 120
min_C = 30

# Travel times (in minutes)
travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Sunset District"): 26,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Sunset District"): 23,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Bayview"): 22
}

# Meeting locations for each friend
location_R = "Mission District"  # Rebecca
location_K = "Bayview"           # Karen
location_C = "Sunset District"   # Carol

# Add availability constraints and minimum duration for meetings
opt.add(S_R >= avail_R_start, E_R <= avail_R_end, E_R - S_R >= min_R)
opt.add(S_K >= avail_K_start, E_K <= avail_K_end, E_K - S_K >= min_K)
opt.add(S_C >= avail_C_start, E_C <= avail_C_end, E_C - S_C >= min_C)

# Ordering variables constraints (each order is in {1,2,3} and they must be distinct)
opt.add(And(order_R >= 1, order_R <= 3))
opt.add(And(order_K >= 1, order_K <= 3))
opt.add(And(order_C >= 1, order_C <= 3))
opt.add(Distinct(order_R, order_K, order_C))

# For the first meeting in the itinerary, account for travel from Union Square
opt.add(Implies(order_R == 1, S_R >= arrival + travel_times[("Union Square", location_R)]))
opt.add(Implies(order_K == 1, S_K >= arrival + travel_times[("Union Square", location_K)]))
opt.add(Implies(order_C == 1, S_C >= arrival + travel_times[("Union Square", location_C)]))

# Helper function to map friend labels to travel times between their meeting locations
def get_travel_time(from_friend, to_friend):
    if from_friend == "R" and to_friend == "K":
        return travel_times[(location_R, location_K)]  # Mission District -> Bayview = 15
    if from_friend == "R" and to_friend == "C":
        return travel_times[(location_R, location_C)]  # Mission District -> Sunset District = 24
    if from_friend == "K" and to_friend == "R":
        return travel_times[(location_K, location_R)]  # Bayview -> Mission District = 13
    if from_friend == "K" and to_friend == "C":
        return travel_times[(location_K, location_C)]  # Bayview -> Sunset District = 23
    if from_friend == "C" and to_friend == "R":
        return travel_times[(location_C, location_R)]  # Sunset District -> Mission District = 24
    if from_friend == "C" and to_friend == "K":
        return travel_times[(location_C, location_K)]  # Sunset District -> Bayview = 22
    return 0

# Add travel constraints for consecutive meetings.
# When meeting i immediately precedes meeting j, enforce that S_j >= E_i + travel_time(i->j).
opt.add(Implies(order_R + 1 == order_K, S_K >= E_R + get_travel_time("R", "K")))
opt.add(Implies(order_R + 1 == order_C, S_C >= E_R + get_travel_time("R", "C")))
opt.add(Implies(order_K + 1 == order_R, S_R >= E_K + get_travel_time("K", "R")))
opt.add(Implies(order_K + 1 == order_C, S_C >= E_K + get_travel_time("K", "C")))
opt.add(Implies(order_C + 1 == order_R, S_R >= E_C + get_travel_time("C", "R")))
opt.add(Implies(order_C + 1 == order_K, S_K >= E_C + get_travel_time("C", "K")))

# Define finish_time as the end time of the meeting scheduled in position 3.
opt.add(finish_time == If(order_R == 3, E_R, If(order_K == 3, E_K, E_C)))

# Set objective: finish as early as possible
opt.minimize(finish_time)

# Check satisfiability and compute the model
if opt.check() == sat:
    m = opt.model()
    
    # Create a schedule list with meeting details including order, start, end and location.
    schedule = []
    schedule.append({
        "person": "Rebecca",
        "order": m[order_R].as_long(),
        "start": m[S_R].as_long(),
        "end": m[E_R].as_long(),
        "location": location_R
    })
    schedule.append({
        "person": "Karen",
        "order": m[order_K].as_long(),
        "start": m[S_K].as_long(),
        "end": m[E_K].as_long(),
        "location": location_K
    })
    schedule.append({
        "person": "Carol",
        "order": m[order_C].as_long(),
        "start": m[S_C].as_long(),
        "end": m[E_C].as_long(),
        "location": location_C
    })
    
    # Sort meetings by their scheduled order
    schedule_sorted = sorted(schedule, key=lambda x: x["order"])
    
    itinerary = []
    for meeting in schedule_sorted:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))