# Z3-based scheduler for meeting David in San Francisco
# Assumptions:
# - Day starts when you arrive at Golden Gate Park at 09:00 (treated as time 0).
# - Travel time Golden Gate Park -> Chinatown: 23 minutes.
# - David is available in Chinatown from 16:00 to 21:45.
# - Goal: meet David for as long as possible, at least 105 minutes.

from z3 import Optimize, Int, sat
import json

def minutes_to_hhmm(minutes_from_0900):
    total = 9*60 + minutes_from_0900  # Convert from offset since 09:00 to absolute minutes since 00:00
    hh = total // 60
    mm = total % 60
    return f"{hh:02d}:{mm:02d}"

def solve():
    # Constants (in minutes relative to 09:00 = 0)
    GGP_ARRIVAL = 0
    TRAVEL_GGP_TO_CT = 23
    DAVID_START = (16 - 9) * 60          # 16:00 relative to 09:00 -> 7*60 = 420
    DAVID_END = (21 - 9) * 60 + 45       # 21:45 relative to 09:00 -> 12*60+45 = 765
    MIN_MEET = 105

    opt = Optimize()

    # Variables: meeting start and end in minutes relative to 09:00
    s = Int('s')  # start time
    e = Int('e')  # end time

    # Constraints:
    # - Must meet within David's availability window
    opt.add(s >= DAVID_START)
    opt.add(e <= DAVID_END)
    # - Travel feasibility: cannot start before we can arrive from Golden Gate Park
    opt.add(s >= GGP_ARRIVAL + TRAVEL_GGP_TO_CT)
    # - Proper interval and minimum meeting length
    opt.add(e > s)
    opt.add(e - s >= MIN_MEET)

    # Objective: maximize meeting duration
    opt.maximize(e - s)

    if opt.check() != sat:
        # If unsat (should not happen with given data), return empty itinerary
        return {"itinerary": []}

    m = opt.model()
    s_val = m[s].as_long()
    e_val = m[e].as_long()

    itinerary = [{
        "action": "meet",
        "person": "David",
        "start_time": minutes_to_hhmm(s_val),
        "end_time": minutes_to_hhmm(e_val)
    }]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result))