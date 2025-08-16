from z3 import Optimize
import json

# We'll represent times as integer minutes after midnight.
# For example, 9:00 AM is 9*60 = 540, 15:30 is 15*60 + 30 = 930, etc.

# Fixed meeting durations (in minutes)
DURATION = {
    "Laura": 30,
    "Thomas": 120,
    "Patricia": 45,
    "Betty": 45,
    "Stephanie": 30
}

# Availability windows (in minutes after midnight)
# Note: if a friend is already present earlier than you arrive, your meeting can only start after your arrival and travel.
AVAILABILITY = {
    "Laura": {"start": 525, "end": 975},       # 08:45 to 16:15 at Nob Hill
    "Thomas": {"start": 930, "end": 1110},       # 15:30 to 18:30 at Bayview
    "Patricia": {"start": 1050, "end": 1320},    # 17:30 to 22:00 at Embarcadero
    "Betty": {"start": 1125, "end": 1305},       # 18:45 to 21:45 at Marina District
    "Stephanie": {"start": 1110, "end": 1305}      # 18:30 to 21:45 at Golden Gate Park
}

# Travel times between locations (in minutes)
# Chosen route (by location):
#  Starting at Fisherman's Wharf, then:
#   Laura is at Nob Hill,
#   Thomas is at Bayview,
#   Patricia is at Embarcadero,
#   Betty is at Marina District,
#   Stephanie is at Golden Gate Park.
TRAVEL = {
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Embarcadero", "Marina District"): 12,
    ("Marina District", "Golden Gate Park"): 18
}

# Initial arrival: you reach Fisherman's Wharf at 9:00 AM = 540 minutes.
arrival_time = 540

# Create an optimizer instance for scheduling
opt = Optimize()

# Create Z3 integer variables for the meeting start times (in minutes after midnight)
L =  int_var =  opt.int_const("L")  # Laura's meeting start at Nob Hill
T =  opt.int_const("T")             # Thomas's meeting start at Bayview
P =  opt.int_const("P")             # Patricia's meeting start at Embarcadero
B =  opt.int_const("B")             # Betty's meeting start at Marina District
S =  opt.int_const("S")             # Stephanie's meeting start at Golden Gate Park

# Add constraints for each meeting to lie completely within the friend’s availability.
# Also include travel from starting location when needed.

# For Laura:
# You depart Fisherman's Wharf at 9:00 and travel to Nob Hill (11 minutes).
opt.add(L >= arrival_time + TRAVEL[("Fisherman's Wharf", "Nob Hill")])
opt.add(L + DURATION["Laura"] <= AVAILABILITY["Laura"]["end"])
# (It is automatically true that L is after 525, since arrival+11 >= 551.)

# For Thomas:
opt.add(T >= AVAILABILITY["Thomas"]["start"])
opt.add(T + DURATION["Thomas"] <= AVAILABILITY["Thomas"]["end"])

# For Patricia:
opt.add(P >= AVAILABILITY["Patricia"]["start"])
opt.add(P + DURATION["Patricia"] <= AVAILABILITY["Patricia"]["end"])

# For Betty:
opt.add(B >= AVAILABILITY["Betty"]["start"])
opt.add(B + DURATION["Betty"] <= AVAILABILITY["Betty"]["end"])

# For Stephanie:
opt.add(S >= AVAILABILITY["Stephanie"]["start"])
opt.add(S + DURATION["Stephanie"] <= AVAILABILITY["Stephanie"]["end"])

# Now add travel constraints between successive meetings on our chosen route:
# Order: Laura (Nob Hill) -> Thomas (Bayview) -> Patricia (Embarcadero) -> Betty (Marina District) -> Stephanie (Golden Gate Park)
opt.add(L + DURATION["Laura"] + TRAVEL[("Nob Hill", "Bayview")] <= T)
opt.add(T + DURATION["Thomas"] + TRAVEL[("Bayview", "Embarcadero")] <= P)
opt.add(P + DURATION["Patricia"] + TRAVEL[("Embarcadero", "Marina District")] <= B)
opt.add(B + DURATION["Betty"] + TRAVEL[("Marina District", "Golden Gate Park")] <= S)

# (Optional) To optimize the schedule we can minimize the final finish time.
# Final finish time = S + duration of Stephanie.
opt.minimize(S + DURATION["Stephanie"])

# Solve the constraints.
if opt.check() == sat:
    m = opt.model()
    L_val = m[L].as_long()
    T_val = m[T].as_long()
    P_val = m[P].as_long()
    B_val = m[B].as_long()
    S_val = m[S].as_long()

    # Helper function to convert minutes to "HH:MM" in 24-hour format.
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    itinerary = []
    itinerary.append({
        "action": "meet",
        "person": "Laura",
        "start_time": format_time(L_val),
        "end_time": format_time(L_val + DURATION["Laura"])
    })
    itinerary.append({
        "action": "meet",
        "person": "Thomas",
        "start_time": format_time(T_val),
        "end_time": format_time(T_val + DURATION["Thomas"])
    })
    itinerary.append({
        "action": "meet",
        "person": "Patricia",
        "start_time": format_time(P_val),
        "end_time": format_time(P_val + DURATION["Patricia"])
    })
    itinerary.append({
        "action": "meet",
        "person": "Betty",
        "start_time": format_time(B_val),
        "end_time": format_time(B_val + DURATION["Betty"])
    })
    itinerary.append({
        "action": "meet",
        "person": "Stephanie",
        "start_time": format_time(S_val),
        "end_time": format_time(S_val + DURATION["Stephanie"])
    })

    schedule = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(schedule, indent=2))
else:
    print("SOLUTION: No valid schedule found")