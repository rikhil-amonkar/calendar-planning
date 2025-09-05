import json
from z3 import Optimize, Int, Bool, If, Implies, And

# Helper functions
def time_to_minutes(tstr):
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input parameters
start_location = "North Beach"
start_time_str = "9:00"

travel_minutes = {
    "North Beach": {"Pacific Heights": 8, "Embarcadero": 6},
    "Pacific Heights": {"North Beach": 9, "Embarcadero": 10},
    "Embarcadero": {"North Beach": 5, "Pacific Heights": 11},
}

participants = [
    {"name": "Mark", "location": "Embarcadero", "window_start": "13:00", "window_end": "17:45", "min_meet": 120},
    {"name": "Karen", "location": "Pacific Heights", "window_start": "18:45", "window_end": "20:15", "min_meet": 90},
]

# Map participants to indices for convenience
p_map = {p["name"]: p for p in participants}

# Convert constants to minutes
START_TIME = time_to_minutes(start_time_str)

# Z3 variables
opt = Optimize()

# Booleans indicating whether to meet each person
meet_mark = Bool("meet_mark")
meet_karen = Bool("meet_karen")

# Start and end times for meetings (in minutes since midnight)
S_mark = Int("S_mark")
E_mark = Int("E_mark")
S_karen = Int("S_karen")
E_karen = Int("E_karen")

# Domain constraints for times
for v in [S_mark, E_mark, S_karen, E_karen]:
    opt.add(v >= 0, v <= 24 * 60)

# Extract participant details
mark = p_map["Mark"]
karen = p_map["Karen"]

# Time windows
mark_ws = time_to_minutes(mark["window_start"])
mark_we = time_to_minutes(mark["window_end"])
karen_ws = time_to_minutes(karen["window_start"])
karen_we = time_to_minutes(karen["window_end"])

# Travel times
t_NB_EMB = travel_minutes[start_location][mark["location"]]
t_NB_PH = travel_minutes[start_location][karen["location"]]
t_EMB_PH = travel_minutes[mark["location"]][karen["location"]]

# Constraints for Mark
opt.add(Implies(meet_mark, And(
    S_mark >= mark_ws,
    E_mark <= mark_we,
    E_mark - S_mark >= mark["min_meet"],
    S_mark >= START_TIME + t_NB_EMB
)))

# If not meeting Mark, set a consistent relationship (no-op duration)
opt.add(Implies(~meet_mark, E_mark == S_mark))

# Constraints for Karen
opt.add(Implies(meet_karen, And(
    S_karen >= karen_ws,
    E_karen <= karen_we,
    E_karen - S_karen >= karen["min_meet"],
    # Travel feasibility: from start if only Karen, or from Mark if both
    S_karen >= If(meet_mark, E_mark + t_EMB_PH, START_TIME + t_NB_PH)
)))

# If not meeting Karen, set a consistent relationship (no-op duration)
opt.add(Implies(~meet_karen, E_karen == S_karen))

# Ensure order and non-overlap if meeting both (redundant given travel, but explicit)
opt.add(Implies(And(meet_mark, meet_karen), S_karen >= E_mark + t_EMB_PH))

# Objectives:
# 1) Maximize number of friends met
friend_count = If(meet_mark, 1, 0) + If(meet_karen, 1, 0)
opt.maximize(friend_count)

# 2) Maximize total meeting duration
total_meeting_minutes = If(meet_mark, E_mark - S_mark, 0) + If(meet_karen, E_karen - S_karen, 0)
opt.maximize(total_meeting_minutes)

# Solve
if opt.check() != 1:
    # Should not occur with given inputs; fallback empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    model = opt.model()
    meet_mark_val = model.evaluate(meet_mark, model_completion=True)
    meet_karen_val = model.evaluate(meet_karen, model_completion=True)

    # Build itinerary entries
    itinerary_entries = []

    if meet_mark_val is not None and meet_mark_val.is_true():
        s = model.evaluate(S_mark, model_completion=True).as_long()
        e = model.evaluate(E_mark, model_completion=True).as_long()
        itinerary_entries.append((
            s,
            {
                "action": "meet",
                "location": mark["location"],
                "person": "Mark",
                "start_time": minutes_to_time(s),
                "end_time": minutes_to_time(e),
            }
        ))

    if meet_karen_val is not None and meet_karen_val.is_true():
        s = model.evaluate(S_karen, model_completion=True).as_long()
        e = model.evaluate(E_karen, model_completion=True).as_long()
        itinerary_entries.append((
            s,
            {
                "action": "meet",
                "location": karen["location"],
                "person": "Karen",
                "start_time": minutes_to_time(s),
                "end_time": minutes_to_time(e),
            }
        ))

    # Sort by start time
    itinerary_entries.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in itinerary_entries]

    print(json.dumps({"itinerary": itinerary}))