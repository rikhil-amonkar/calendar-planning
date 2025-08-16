# Solve the SF day-meet scheduling problem using Z3 and output a JSON itinerary.
# Objectives:
# 1) Maximize number of friends met (Laura, Anthony).
# 2) Subject to (1), maximize total meeting time.
# 3) Subject to (1) and (2), meet Laura as early as possible (minimize Laura start),
#    which in effect minimizes Anthony duration and pushes Anthony earlier.

import json
from z3 import Optimize, Int, Bool, If, Implies, And

# Time helper (minutes from midnight)
def hm_to_min(h, m):
    return h * 60 + m

def fmt_min_to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Constants
CASTRO = "Castro"
MISSION = "Mission District"
FINANCIAL = "Financial District"

# Travel times (minutes)
travel = {
    (CASTRO, MISSION): 7,
    (MISSION, CASTRO): 7,
    (CASTRO, FINANCIAL): 20,
    (FINANCIAL, CASTRO): 23,
    (MISSION, FINANCIAL): 17,
    (FINANCIAL, MISSION): 17,
}

# Availability windows and minimum durations
# Times in minutes since midnight
arrive_castro = hm_to_min(9, 0)

laura_loc = MISSION
laura_start = hm_to_min(12, 15)
laura_end = hm_to_min(19, 45)
laura_min = 75

anthony_loc = FINANCIAL
anthony_start = hm_to_min(12, 30)
anthony_end = hm_to_min(14, 45)
anthony_min = 30

opt = Optimize()
opt.set(priority='lex')  # Lexicographic optimization

# Decision variables
L_start = Int("L_start")
L_end = Int("L_end")
A_start = Int("A_start")
A_end = Int("A_end")

meet_L = Bool("meet_L")
meet_A = Bool("meet_A")

# Ordering when both are met
A_first = Bool("A_first")

# Basic domains
opt.add(L_end >= L_start, A_end >= A_start)

# Availability and minimum duration constraints
# If meeting, it must be within availability window and meet minimum duration
opt.add(Implies(meet_L, And(L_start >= laura_start, L_end <= laura_end, (L_end - L_start) >= laura_min)))
opt.add(Implies(meet_A, And(A_start >= anthony_start, A_end <= anthony_end, (A_end - A_start) >= anthony_min)))

# If not meeting, duration is zero (collapse interval)
opt.add(Implies(~meet_L, L_end == L_start))
opt.add(Implies(~meet_A, A_end == A_start))

# Travel feasibility from starting point (Castro) to the first meeting
# If only Laura is met
opt.add(Implies(And(meet_L, ~meet_A),
                L_start >= arrive_castro + travel[(CASTRO, laura_loc)]))
# If only Anthony is met
opt.add(Implies(And(meet_A, ~meet_L),
                A_start >= arrive_castro + travel[(CASTRO, anthony_loc)]))

# If both are met, enforce ordering and travel between meetings, and feasibility from Castro
opt.add(Implies(And(meet_A, meet_L, A_first),
                And(
                    A_start >= arrive_castro + travel[(CASTRO, anthony_loc)],
                    L_start >= A_end + travel[(FINANCIAL, MISSION)]
                )))

opt.add(Implies(And(meet_A, meet_L, ~A_first),
                And(
                    L_start >= arrive_castro + travel[(CASTRO, laura_loc)],
                    A_start >= L_end + travel[(MISSION, FINANCIAL)]
                )))

# Objective 1: maximize number of friends met
count_met = If(meet_L, 1, 0) + If(meet_A, 1, 0)
opt.maximize(count_met)

# Objective 2: maximize total meeting time
total_minutes = (L_end - L_start) + (A_end - A_start)
opt.maximize(total_minutes)

# Objective 3: earliest Laura start time (encourage Anthony as early and as short as possible when optimal)
# We minimize L_start by maximizing negative L_start (Optimize only supports maximize/minimize,
# Python API supports both, so we can directly minimize).
opt.minimize(L_start)

# Solve
res = opt.check()
assert str(res) == "sat", "No feasible schedule found."

m = opt.model()

meet_L_val = bool(m.eval(meet_L, model_completion=True))
meet_A_val = bool(m.eval(meet_A, model_completion=True))

itinerary = []

if meet_A_val:
    A_s = m.eval(A_start, model_completion=True).as_long()
    A_e = m.eval(A_end, model_completion=True).as_long()
    itinerary.append({
        "action": "meet",
        "person": "Anthony",
        "start_time": fmt_min_to_hhmm(A_s),
        "end_time": fmt_min_to_hhmm(A_e)
    })

if meet_L_val:
    L_s = m.eval(L_start, model_completion=True).as_long()
    L_e = m.eval(L_end, model_completion=True).as_long()
    itinerary.append({
        "action": "meet",
        "person": "Laura",
        "start_time": fmt_min_to_hhmm(L_s),
        "end_time": fmt_min_to_hhmm(L_e)
    })

# Sort by start_time just in case
itinerary.sort(key=lambda x: x["start_time"])

print(json.dumps({"itinerary": itinerary}))