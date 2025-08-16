from z3 import Optimize, Int, Bool, If, Implies, Not, sat
import json

# Convert time strings to minutes from midnight:
# 8:15  -> 8*60+15 = 495, 9:00 -> 540, 9:23 -> 9*60+23 = 563, 10:08 -> 608,
# 12:00 -> 720, 13:30 -> 810, 15:00 -> 900, 19:00 -> 1140.

opt = Optimize()

# Define integer variables for the start and end times (in minutes from midnight)
startB = Int("startB")  # Meeting start for Barbara at Golden Gate Park.
endB   = Int("endB")    # Meeting end for Barbara.
startK = Int("startK")  # Meeting start for Kenneth at Chinatown.
endK   = Int("endK")    # Meeting end for Kenneth.

# A variable F representing the overall finish time.
F = Int("F")

# A boolean to choose the schedule order:
# When order == True, we schedule the meeting with Barbara first then Kenneth.
# When order == False, Kenneth first then Barbara.
order = Bool("order")

# Constants (in minutes)
FD_arrival = 540           # Arrive at Financial District at 9:00.
GGP_travel_from_FD = 23    # FD -> Golden Gate Park.
Ch_travel_from_FD = 5      # FD -> Chinatown.
GGP_to_Ch_travel = 23      # Golden Gate Park -> Chinatown.
Ch_to_GGP_travel = 23      # Chinatown -> Golden Gate Park.
# Friend available windows:
Barbara_open = 495       # 8:15 for Barbara at Golden Gate Park.
Barbara_close = 1140     # 19:00 for Barbara.
Kenneth_open  = 720      # 12:00 for Kenneth at Chinatown.
Kenneth_close = 900      # 15:00 for Kenneth.
# Minimum meeting durations:
Barbara_duration = 45
Kenneth_duration = 90

# ----------------------------
# CASE 1: Schedule order: Barbara first, then Kenneth.
# Travel constraints when meeting Barbara first:
#   Leave FD at 9:00 and travel to Golden Gate Park (23 minutes) so:
opt.add(Implies(order, startB >= FD_arrival + GGP_travel_from_FD))
# Meeting with Barbara must last 45 minutes and end before her close time:
opt.add(Implies(order, endB >= startB + Barbara_duration))
opt.add(Implies(order, endB <= Barbara_close))
# Then travel from Golden Gate Park to Chinatown takes 23 minutes.
opt.add(Implies(order, startK >= endB + GGP_to_Ch_travel))
# Kenneth is available only starting at 12:00:
opt.add(Implies(order, startK >= Kenneth_open))
# Kenneth meeting must last at least 90 minutes and finish by 15:00:
opt.add(Implies(order, endK >= startK + Kenneth_duration))
opt.add(Implies(order, endK <= Kenneth_close))

# ----------------------------
# CASE 2: Schedule order: Kenneth first, then Barbara.
# Travel constraints when meeting Kenneth first:
#   Leave FD at 9:00 and travel to Chinatown (5 minutes):
opt.add(Implies(Not(order), startK >= FD_arrival + Ch_travel_from_FD))
# Kenneth meeting must last at least 90 minutes and finish by 15:00:
opt.add(Implies(Not(order), endK >= startK + Kenneth_duration))
opt.add(Implies(Not(order), endK <= Kenneth_close))
# Then travel from Chinatown to Golden Gate Park takes 23 minutes.
opt.add(Implies(Not(order), startB >= endK + Ch_to_GGP_travel))
# Barbara meeting must last at least 45 minutes and finish by 19:00.
opt.add(Implies(Not(order), endB >= startB + Barbara_duration))
opt.add(Implies(Not(order), endB <= Barbara_close))

# Final finish time: if Barbara is first then finish time is Kenneth's end; otherwise it's Barbara's end.
opt.add(F == If(order, endK, endB))

# We want to finish as early as possible (minimizing idle/waiting time).
opt.minimize(F)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    # Determine the order chosen:
    order_val = model.evaluate(order)
    if order_val:
        # Order: Barbara then Kenneth.
        b_start = model.evaluate(startB).as_long()
        b_end   = model.evaluate(endB).as_long()
        k_start = model.evaluate(startK).as_long()
        k_end   = model.evaluate(endK).as_long()
    else:
        # Order: Kenneth then Barbara.
        k_start = model.evaluate(startK).as_long()
        k_end   = model.evaluate(endK).as_long()
        b_start = model.evaluate(startB).as_long()
        b_end   = model.evaluate(endB).as_long()

    # Helper function to format time from minutes to "HH:MM".
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    itinerary = [
        {"action": "meet", "person": "Barbara", "start_time": format_time(b_start), "end_time": format_time(b_end)},
        {"action": "meet", "person": "Kenneth", "start_time": format_time(k_start), "end_time": format_time(k_end)}
    ]

    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution was found")