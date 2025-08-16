from z3 import *
import json

def minutes_to_time_str(minutes):
    """Converts minutes since midnight into a HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Create the Z3 solver.
solver = Solver()

# ---------------------------------------------------------------------------
# VARIABLES
# ---------------------------------------------------------------------------
# Start times for meetings (in minutes since midnight)
s_emily   = Int("s_emily")    # Meeting with Emily (at Presidio)
s_joseph  = Int("s_joseph")   # Meeting with Joseph (at Richmond District)
s_melissa = Int("s_melissa")  # Meeting with Melissa (at Financial District)

# Order variables define the sequence (0 = first, 1 = second, 2 = third)
order_emily   = Int("order_emily")
order_joseph  = Int("order_joseph")
order_melissa = Int("order_melissa")

# Meeting durations (minutes)
d_emily   = 105  # Emily requires at least 105 minutes together
d_joseph  = 120  # Joseph requires at least 120 minutes together
d_melissa = 75   # Melissa requires at least 75 minutes together

# Availability windows (in minutes since midnight)
avail_start_emily   = 16 * 60 + 15  # 16:15 => 975
avail_end_emily     = 21 * 60       # 21:00 => 1260

avail_start_joseph  = 17 * 60 + 15  # 17:15 => 1035
avail_end_joseph    = 22 * 60       # 22:00 => 1320

avail_start_melissa = 15 * 60 + 45  # 15:45 => 945
avail_end_melissa   = 21 * 60 + 45  # 21:45 => 1305

# We start at Fisherman's Wharf at 9:00AM (9*60 = 540 minutes)
start_init = 9 * 60  # 540 minutes

# Initial travel times (from Fisherman's Wharf to each meeting location)
init_travel = {
    "emily":   17,  # Fisherman's Wharf -> Presidio
    "joseph":  18,  # Fisherman's Wharf -> Richmond District
    "melissa": 11   # Fisherman's Wharf -> Financial District
}

# Travel times between the meeting locations (for consecutive meetings)
# (from_person, to_person) : travel time in minutes
travel = {
    ("emily", "joseph"): 7,    # Presidio -> Richmond District
    ("emily", "melissa"): 23,  # Presidio -> Financial District
    ("joseph", "emily"): 7,    # Richmond District -> Presidio
    ("joseph", "melissa"): 22, # Richmond District -> Financial District
    ("melissa", "emily"): 22,  # Financial District -> Presidio
    ("melissa", "joseph"): 21  # Financial District -> Richmond District
}

# ---------------------------------------------------------------------------
# CONSTRAINTS
# ---------------------------------------------------------------------------
# 1. Order variables: each meeting position is in {0,1,2} and all are distinct.
solver.add(And(order_emily >= 0, order_emily <= 2))
solver.add(And(order_joseph >= 0, order_joseph <= 2))
solver.add(And(order_melissa >= 0, order_melissa <= 2))
solver.add(Distinct(order_emily, order_joseph, order_melissa))

# 2. Availability constraints for each meeting:
solver.add(s_emily >= avail_start_emily)
solver.add(s_emily + d_emily <= avail_end_emily)

solver.add(s_joseph >= avail_start_joseph)
solver.add(s_joseph + d_joseph <= avail_end_joseph)

solver.add(s_melissa >= avail_start_melissa)
solver.add(s_melissa + d_melissa <= avail_end_melissa)

# 3. If a meeting is the first one of the day, its start time must be no earlier
#    than the time to travel from Fisherman's Wharf.
solver.add(If(order_emily == 0, s_emily >= start_init + init_travel["emily"], True))
solver.add(If(order_joseph == 0, s_joseph >= start_init + init_travel["joseph"], True))
solver.add(If(order_melissa == 0, s_melissa >= start_init + init_travel["melissa"], True))

# 4. For consecutive meetings, if meeting A immediately precedes meeting B, then B's
#    start time must be at least the end time of A plus the travel time from A to B.
solver.add(If(order_emily + 1 == order_joseph,
              s_joseph >= s_emily + d_emily + travel[("emily", "joseph")],
              True))
solver.add(If(order_emily + 1 == order_melissa,
              s_melissa >= s_emily + d_emily + travel[("emily", "melissa")],
              True))
solver.add(If(order_joseph + 1 == order_emily,
              s_emily >= s_joseph + d_joseph + travel[("joseph", "emily")],
              True))
solver.add(If(order_joseph + 1 == order_melissa,
              s_melissa >= s_joseph + d_joseph + travel[("joseph", "melissa")],
              True))
solver.add(If(order_melissa + 1 == order_emily,
              s_emily >= s_melissa + d_melissa + travel[("melissa", "emily")],
              True))
solver.add(If(order_melissa + 1 == order_joseph,
              s_joseph >= s_melissa + d_melissa + travel[("melissa", "joseph")],
              True))

# ---------------------------------------------------------------------------
# SOLVE & OUTPUT
# ---------------------------------------------------------------------------
if solver.check() == sat:
    model = solver.model()
    
    # Extract meeting times and orders.
    meetings = {
        "emily": {
            "start": model[s_emily].as_long(),
            "end": model[s_emily].as_long() + d_emily,
            "order": model[order_emily].as_long()
        },
        "joseph": {
            "start": model[s_joseph].as_long(),
            "end": model[s_joseph].as_long() + d_joseph,
            "order": model[order_joseph].as_long()
        },
        "melissa": {
            "start": model[s_melissa].as_long(),
            "end": model[s_melissa].as_long() + d_melissa,
            "order": model[order_melissa].as_long()
        }
    }
    
    # Sort meetings according to the scheduled order.
    sorted_meetings = sorted(meetings.items(), key=lambda x: x[1]["order"])
    
    # Map lowercase keys to proper names.
    proper_names = {"emily": "Emily", "joseph": "Joseph", "melissa": "Melissa"}
    
    itinerary = []
    for person, info in sorted_meetings:
        itinerary.append({
            "action": "meet",
            "person": proper_names[person],
            "start_time": minutes_to_time_str(info["start"]),
            "end_time": minutes_to_time_str(info["end"])
        })
    
    # Build and print the JSON output.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")