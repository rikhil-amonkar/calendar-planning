# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, And, sat
import json

def minutes(hh, mm):
    return hh * 60 + mm

def fmt_time(total_minutes):
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

def solve_itinerary():
    # Constants
    RH_ARRIVAL = minutes(9, 0)          # Arrive at Russian Hill at 09:00
    TRAVEL_RH_TO_RD = 14                 # Russian Hill -> Richmond District
    # TRAVEL_RD_TO_RH = 13               # Not needed for this meeting-only schedule

    BARBARA_START = minutes(13, 15)      # 13:15
    BARBARA_END = minutes(18, 15)        # 18:15
    MIN_MEET_MINUTES = 45

    # Decision variables
    start = Int("start")  # meeting start time in minutes since midnight
    end = Int("end")      # meeting end time in minutes since midnight
    depart_rh = Int("depart_rh")  # time leaving Russian Hill to head to Richmond

    opt = Optimize()

    # Constraints:
    # 1) Meeting within Barbara's availability window.
    opt.add(start >= BARBARA_START)
    opt.add(end <= BARBARA_END)
    opt.add(end > start)
    opt.add(end - start >= MIN_MEET_MINUTES)

    # 2) Travel feasibility: must be able to depart RH (no earlier than 09:00) and arrive before meeting starts.
    opt.add(depart_rh >= RH_ARRIVAL)
    opt.add(depart_rh + TRAVEL_RH_TO_RD <= start)

    # Objective: maximize total meeting time with Barbara.
    opt.maximize(end - start)

    if opt.check() != sat:
        return {"itinerary": []}

    m = opt.model()
    start_val = m[start].as_long()
    end_val = m[end].as_long()

    itinerary = [{
        "action": "meet",
        "person": "Barbara",
        "start_time": fmt_time(start_val),
        "end_time": fmt_time(end_val)
    }]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))