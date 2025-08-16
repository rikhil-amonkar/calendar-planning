# Z3-based scheduler for meeting friends in San Francisco
# Goal: maximize number of meetings (here, only Joshua is available), then maximize meeting duration
# Constraints:
# - Arrive Sunset District at 09:00 (540 minutes)
# - Travel Sunset District -> Golden Gate Park: 11 minutes
# - Joshua available at Golden Gate Park: 20:45 (1245) to 21:45 (1305)
# - Meet Joshua at least 15 minutes
# Output: JSON itinerary

from z3 import Optimize, Int
import json

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def solve_schedule():
    # Constants
    DAY_START = 0
    DAY_END = 24 * 60

    arrival_sunset = 9 * 60  # 09:00
    t_sunset_to_ggp = 11     # minutes

    joshua_start = 20 * 60 + 45  # 20:45
    joshua_end = 21 * 60 + 45    # 21:45
    min_meet = 15

    # Decision variables: meeting with Joshua at Golden Gate Park
    meet_start = Int("meet_start")  # minutes from midnight
    meet_end = Int("meet_end")      # minutes from midnight

    opt = Optimize()

    # Domain bounds
    opt.add(meet_start >= DAY_START, meet_end <= DAY_END, meet_start < meet_end)

    # Availability and travel feasibility
    opt.add(meet_start >= joshua_start)
    opt.add(meet_end <= joshua_end)
    opt.add(meet_end - meet_start >= min_meet)

    # Must be able to reach Golden Gate Park from Sunset after arriving at 09:00
    opt.add(meet_start >= arrival_sunset + t_sunset_to_ggp)

    # Optimization: maximize duration (with one friend, meeting count is implicitly 1 if feasible)
    duration = meet_end - meet_start
    opt.maximize(duration)

    if opt.check() != sat:
        # No feasible schedule
        return {"itinerary": []}

    model = opt.model()
    s = model[meet_start].as_long()
    e = model[meet_end].as_long()

    itinerary = {
        "itinerary": [
            {
                "action": "meet",
                "person": "Joshua",
                "start_time": minutes_to_hhmm(s),
                "end_time": minutes_to_hhmm(e),
            }
        ]
    }
    return itinerary

if __name__ == "__main__":
    result = solve_schedule()
    # Print the JSON itinerary (matches the required output format)
    print(json.dumps(result))