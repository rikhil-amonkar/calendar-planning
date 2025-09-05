import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def main():
    # Input parameters (as variables)
    # Locations
    RUSSIAN_HILL = "Russian Hill"
    PACIFIC_HEIGHTS = "Pacific Heights"

    # Travel times (minutes)
    travel_RH_to_PH = 7
    travel_PH_to_RH = 7

    # Arrival time at Russian Hill
    arrive_RH = minutes(9, 0)

    # Barbara's availability at Pacific Heights
    barbara_name = "Barbara"
    barbara_loc = PACIFIC_HEIGHTS
    barbara_start = minutes(7, 15)
    barbara_end = minutes(22, 0)
    min_meet_duration = 60  # minutes

    # Z3 Optimize model
    opt = Optimize()

    # Decision variables for Barbara meeting
    start_b = Int("start_b")     # meeting start time (minutes from midnight)
    end_b = Int("end_b")         # meeting end time
    meet_b = Int("meet_b")       # 0/1 whether we meet Barbara
    duration_b = Int("duration_b")

    # Variable domains
    opt.add(And(meet_b >= 0, meet_b <= 1))
    opt.add(And(start_b >= 0, start_b <= 24 * 60))
    opt.add(And(end_b >= 0, end_b <= 24 * 60))
    opt.add(duration_b == If(meet_b == 1, end_b - start_b, 0))

    # If meeting Barbara, enforce feasibility with travel and availability
    opt.add(Implies(meet_b == 1, start_b >= arrive_RH + travel_RH_to_PH))
    opt.add(Implies(meet_b == 1, start_b >= barbara_start))
    opt.add(Implies(meet_b == 1, end_b <= barbara_end))
    opt.add(Implies(meet_b == 1, end_b - start_b >= min_meet_duration))

    # If not meeting, ensure start=end to eliminate spurious durations
    opt.add(Implies(meet_b == 0, end_b == start_b))

    # Objectives:
    # 1) Maximize number of friends met (here only Barbara -> maximize meet_b)
    # 2) Maximize total meeting time (duration_b)
    # 3) Minimize start time (earlier start preferred in case of ties)
    opt.maximize(meet_b)
    opt.maximize(duration_b)
    opt.minimize(start_b)

    result = {"itinerary": []}

    if opt.check() == sat:
        model = opt.model()
        if model[meet_b].as_long() == 1:
            s = model[start_b].as_long()
            e = model[end_b].as_long()
            result["itinerary"].append({
                "action": "meet",
                "location": barbara_loc,
                "person": barbara_name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()