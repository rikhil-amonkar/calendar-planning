from z3 import *
import json

# We measure time in minutes relative to 9:00.
# Thus, 0 represents 09:00 and 240 represents 13:00.
# Friend availabilities:
#   • Richard is at Union Square from –15 to 240 (i.e. available at 9:00, since he’s there from 8:45)
#   • Charles is at Presidio from 45 to 240 (i.e. available starting at 9:45)
#
# Travel times (in minutes) between locations:
#   Bayview -> Union Square: 17
#   Bayview -> Presidio: 31
#   Union Square -> Presidio: 24
#   Presidio -> Union Square: 22
#
# Our “ideal” goal is to have a “meeting” (a block when you are present at your friend’s location)
# with each friend lasting at least 120 minutes.
#
# But note: if you try a simple sequential schedule you get:
#   Option 1 (Richard then Charles):
#     • Leave Bayview at 9:00, arrive at Union Square at 9:17.
#     • Meeting Richard for 120 minutes → 09:17 to 11:17.
#     • Travel from Union Square to Presidio takes 24 minutes → arrive at 11:41.
#     • Meeting Charles would then run 11:41 to 13:00 (only 79 minutes).
#
#   Option 2 (Charles then Richard):
#     • Leave Bayview at 9:00; travel to Presidio takes 31 minutes,
#       but Charles is not available until 9:45 so you begin at 9:45.
#     • Meeting Charles for 120 minutes → 9:45 to 11:45.
#     • Travel from Presidio to Union Square takes 22 minutes → arrive at 11:45+22 = 12:07.
#     • Meeting Richard from 12:07 to 13:00 (only 53 minutes).
#
# Hence it is impossible to get a full 120‐minute meeting with both friends.
#
# We build a Z3 optimization model that “softly” penalizes any shortfall below 120 minutes
# for each meeting. In addition, we allow the ordering of visits to be chosen:
#   • order = True means: go from Bayview -> Union Square -> Presidio (meet Richard then Charles)
#   • order = False means: go from Bayview -> Presidio -> Union Square (meet Charles then Richard)
#
# We then minimize the total “slack”, where for each friend the slack is
#     slack = max(0, 120 – (meeting_end – meeting_start) )
# so that a slack of 0 means the desired 120 minutes have been met.

def minutes_to_HHMM(m):
    # m is minutes after 9:00. We add 9*60 to get absolute minutes in the day.
    total = 9 * 60 + m
    h = total // 60
    mm = total % 60
    return f"{h:02d}:{mm:02d}"

# Create an Optimize() object
opt = Optimize()

# Decision variables for meeting start and end times (in minutes from 9:00).
r_start = Int('r_start')  # when meeting Richard at Union Square starts
r_end   = Int('r_end')    # when meeting Richard ends
c_start = Int('c_start')  # when meeting Charles at Presidio starts
c_end   = Int('c_end')    # when meeting Charles ends

# A Boolean to choose the travel order:
#   True  => Order1: Bayview -> Union Square -> Presidio (Richard then Charles)
#   False => Order2: Bayview -> Presidio -> Union Square (Charles then Richard)
order = Bool('order')

# Order1 constraints: (Richard then Charles)
#  • You start at Bayview at 0.
#  • You must travel to Union Square (17 minutes) so the meeting with Richard cannot start before 17.
#  • Richard is available until 13:00 (i.e. minute 240).
#  • After finishing with Richard, you travel to Presidio (24 minutes).
#  • Charles is at Presidio from minute 45 on.
order1 = And(
    r_start >= 17,           # Bayview->Union Square = 17 minutes
    r_end >= r_start,        # nonnegative meeting duration
    r_end <= 240,            # must finish before 13:00
    c_start >= r_end + 24,   # travel from Union Square to Presidio takes 24 minutes
    c_start >= 45,           # Charles is only available from 9:45 (minute 45)
    c_end >= c_start,        # nonnegative meeting duration
    c_end <= 240             # must finish before 13:00
)

# Order2 constraints: (Charles then Richard)
#  • Travel from Bayview to Presidio takes 31 minutes, but because Charles arrives only from 45,
#    we impose c_start >= 45.
#  • After meeting Charles, you travel from Presidio to Union Square (22 minutes)
order2 = And(
    c_start >= 45,
    c_end >= c_start,
    c_end <= 240,
    r_start >= c_end + 22,   # travel from Presidio to Union Square takes 22 minutes
    r_end >= r_start,
    r_end <= 240
)

# Enforce the constraints corresponding to the chosen order.
opt.add(If(order, order1, order2))

# Define each meeting’s duration.
dur_R = r_end - r_start  # Duration of meeting with Richard
dur_C = c_end - c_start  # Duration of meeting with Charles

# Define slack variables (deficit below the desired 120 minutes).
slack_R = If(dur_R < 120, 120 - dur_R, 0)
slack_C = If(dur_C < 120, 120 - dur_C, 0)
total_slack = slack_R + slack_C

# Our objective is to minimize total slack. (If total_slack==0 then both meetings get at least 120 minutes.)
# (Since it is impossible to have both meetings last 120 minutes given the travel requirements,
# the optimal total slack will be > 0.)
opt.minimize(total_slack)

# For a well‐defined schedule we restrict the meeting times to be within the planning interval.
opt.add(r_start >= 0, r_end >= 0, c_start >= 0, c_end >= 0)

# Check satisfiability and get the optimum model.
if opt.check() == sat:
    m = opt.model()
    
    # Decide which order was chosen.
    order_val = m.evaluate(order)
    
    # Get integer values (minutes relative to 9:00)
    r_start_val = m[r_start].as_long()
    r_end_val   = m[r_end].as_long()
    c_start_val = m[c_start].as_long()
    c_end_val   = m[c_end].as_long()
    
    # Build the itinerary depending on the order.
    itinerary = []
    if is_true(order_val):
        # Order1: Meet Richard then Charles.
        itinerary.append({
          "action": "meet",
          "person": "Richard",
          "start_time": minutes_to_HHMM(r_start_val),
          "end_time": minutes_to_HHMM(r_end_val)
        })
        itinerary.append({
          "action": "meet",
          "person": "Charles",
          "start_time": minutes_to_HHMM(c_start_val),
          "end_time": minutes_to_HHMM(c_end_val)
        })
    else:
        # Order2: Meet Charles then Richard.
        itinerary.append({
          "action": "meet",
          "person": "Charles",
          "start_time": minutes_to_HHMM(c_start_val),
          "end_time": minutes_to_HHMM(c_end_val)
        })
        itinerary.append({
          "action": "meet",
          "person": "Richard",
          "start_time": minutes_to_HHMM(r_start_val),
          "end_time": minutes_to_HHMM(r_end_val)
        })
    
    # Produce final JSON output.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No feasible solution found.")