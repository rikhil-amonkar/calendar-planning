from z3 import *
import json

# Helper function to convert minutes since midnight to "HH:MM" string.
def to_time_str(t):
    # t is an integer representing minutes since midnight.
    hours = t // 60
    minutes = t % 60
    return f"{hours:02d}:{minutes:02d}"

# Create a Z3 solver.
solver = Solver()

# Define meeting time variables for each friend.
# Times are in minutes since midnight.
# Arrival: 9:00 AM = 540 minutes.
# Windows (in minutes):
#   Sarah: available 10:45 (645) to 19:00 (1140), duration >= 30
#   Richard: available 11:45 (705) to 15:45 (945), duration >= 90
#   Elizabeth: available 11:00 (660) to 17:15 (1035), duration >= 120
#   Michelle: available 18:15 (1095) to 20:45 (1245), duration >= 90

s_start = Int('s_start')
s_end   = Int('s_end')
r_start = Int('r_start')
r_end   = Int('r_end')
e_start = Int('e_start')
e_end   = Int('e_end')
m_start = Int('m_start')
m_end   = Int('m_end')

# Order variables: each meeting gets a position 1..4 in the itinerary.
ord_s = Int('ord_s')
ord_r = Int('ord_r')
ord_e = Int('ord_e')
ord_m = Int('ord_m')

# Add domains for the meeting start times (within the friend windows) and durations.
solver.add(s_start >= 645, s_end <= 1140, s_end - s_start >= 30)  # Sarah (Sunset District)
solver.add(r_start >= 705, r_end <= 945,  r_end - r_start >= 90)   # Richard (Haight-Ashbury)
solver.add(e_start >= 660, e_end <= 1035, e_end - e_start >= 120)   # Elizabeth (Mission District)
solver.add(m_start >= 1095, m_end <= 1245, m_end - m_start >= 90)   # Michelle (Golden Gate Park)

# Domain for order variables (positions 1 through 4).
solver.add(And(ord_s >= 1, ord_s <= 4))
solver.add(And(ord_r >= 1, ord_r <= 4))
solver.add(And(ord_e >= 1, ord_e <= 4))
solver.add(And(ord_m >= 1, ord_m <= 4))
solver.add(Distinct(ord_s, ord_r, ord_e, ord_m))

# Define travel times (in minutes) as given.
# The keys are (from_location, to_location). Locations:
#   "Richmond", "Sunset", "Haight", "Mission", "Golden"
travel = {
    ("Richmond", "Sunset"): 11,
    ("Richmond", "Haight"): 10,
    ("Richmond", "Mission"): 20,
    ("Richmond", "Golden"): 9,
    ("Sunset", "Richmond"): 12,
    ("Sunset", "Haight"): 15,
    ("Sunset", "Mission"): 24,
    ("Sunset", "Golden"): 11,
    ("Haight", "Richmond"): 10,
    ("Haight", "Sunset"): 15,
    ("Haight", "Mission"): 11,
    ("Haight", "Golden"): 7,
    ("Mission", "Richmond"): 20,
    ("Mission", "Sunset"): 24,
    ("Mission", "Haight"): 12,
    ("Mission", "Golden"): 17,
    ("Golden", "Richmond"): 7,
    ("Golden", "Sunset"): 10,
    ("Golden", "Haight"): 7,
    ("Golden", "Mission"): 17
}

# Map each friend to their meeting location.
locations = {
    "Sarah": "Sunset",
    "Richard": "Haight",
    "Elizabeth": "Mission",
    "Michelle": "Golden"
}

# For each meeting, if it is the first in the itinerary, then you must travel from Richmond District.
solver.add(Implies(ord_s == 1, 540 + travel[("Richmond", locations["Sarah"])] <= s_start))
solver.add(Implies(ord_r == 1, 540 + travel[("Richmond", locations["Richard"])] <= r_start))
solver.add(Implies(ord_e == 1, 540 + travel[("Richmond", locations["Elizabeth"])] <= e_start))
solver.add(Implies(ord_m == 1, 540 + travel[("Richmond", locations["Michelle"])] <= m_start))

# Define a helper function to add ordering constraints between two meetings.
def add_order_constraint(ord_a, start_a, end_a, loc_a, ord_b, start_b, end_b, loc_b):
    # If meeting A is scheduled before meeting B, then the end time of A plus travel time from A to B
    # must be less than or equal to the start time of B.
    solver.add(Implies(ord_a < ord_b, end_a + travel[(loc_a, loc_b)] <= start_b))
    # Also add the reverse ordering (if B comes before A).
    solver.add(Implies(ord_b < ord_a, end_b + travel[(loc_b, loc_a)] <= start_a))

# Add ordering constraints for every pair of meetings.
add_order_constraint(ord_s, s_start, s_end, locations["Sarah"],
                     ord_r, r_start, r_end, locations["Richard"])
add_order_constraint(ord_s, s_start, s_end, locations["Sarah"],
                     ord_e, e_start, e_end, locations["Elizabeth"])
add_order_constraint(ord_s, s_start, s_end, locations["Sarah"],
                     ord_m, m_start, m_end, locations["Michelle"])
add_order_constraint(ord_r, r_start, r_end, locations["Richard"],
                     ord_e, e_start, e_end, locations["Elizabeth"])
add_order_constraint(ord_r, r_start, r_end, locations["Richard"],
                     ord_m, m_start, m_end, locations["Michelle"])
add_order_constraint(ord_e, e_start, e_end, locations["Elizabeth"],
                     ord_m, m_start, m_end, locations["Michelle"])

# (Optional) You can add additional constraints to “pin down” a likely solution.
# For instance, we can force an ordering that we believe is natural:
# Sarah -> Richard -> Elizabeth -> Michelle.
solver.add(ord_s == 1, ord_r == 2, ord_e == 3, ord_m == 4)

# For a feasible solution, we can also fix meeting start times close to the earliest possible.
# Sarah: earliest start is 645, so set s_start = 645 and s_end = 645 + 30.
solver.add(s_start == 645, s_end == 675)
# Richard: must wait until arrival from Sarah. From Sarah (Sunset) finishing at 675, plus travel (Sunset -> Haight) = 15, earliest arrival = 690.
# But Richard is only available starting at 705. So set:
solver.add(r_start == 705, r_end == 795)
# Elizabeth: After Richard, travel (Haight -> Mission) = 11 so earliest start is 795 + 11 = 806.
solver.add(e_start == 806, e_end == 926)
# Michelle: Although travel from Elizabeth may allow an earlier arrival, Michelle is available starting 18:15 (1095).
solver.add(m_start == 1095, m_end == 1185)

# Check the model.
if solver.check() == sat:
    model = solver.model()
    # Build itinerary list sorted by the order variables.
    meetings = [
        {"person": "Sarah", "start": model[s_start].as_long(), "end": model[s_end].as_long(), "order": model[ord_s].as_long()},
        {"person": "Richard", "start": model[r_start].as_long(), "end": model[r_end].as_long(), "order": model[ord_r].as_long()},
        {"person": "Elizabeth", "start": model[e_start].as_long(), "end": model[e_end].as_long(), "order": model[ord_e].as_long()},
        {"person": "Michelle", "start": model[m_start].as_long(), "end": model[m_end].as_long(), "order": model[ord_m].as_long()}
    ]
    meetings.sort(key=lambda x: x["order"])
    
    # Prepare the final itinerary in the required JSON format.
    itinerary = []
    for meet in meetings:
        itinerary.append({
            "action": "meet",
            "person": meet["person"],
            "start_time": to_time_str(meet["start"]),
            "end_time": to_time_str(meet["end"])
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")