# Requires: z3-solver
# pip install z3-solver
from z3 import *
import json

def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def solve_itinerary():
    # Constants (minutes from midnight)
    DAY_START = 0
    DAY_END = 24 * 60

    # Locations and travel (in minutes)
    FW_to_NH = 11  # Fisherman's Wharf to Nob Hill
    # NH_to_FW = 11  # Not needed for this task

    # Arrival
    arrive_FW = 9 * 60  # 09:00

    # Kenneth availability at Nob Hill
    KENNETH_START = 14 * 60 + 15  # 14:15
    KENNETH_END = 19 * 60 + 45    # 19:45
    MIN_MEET_KENNETH = 90

    opt = Optimize()

    meet_kenneth = Bool("meet_kenneth")
    k_start = Int("k_start")
    k_end = Int("k_end")

    # Variable domains
    opt.add(k_start >= DAY_START, k_start <= DAY_END)
    opt.add(k_end >= DAY_START, k_end <= DAY_END)

    # If meeting Kenneth, enforce availability, travel, and duration constraints
    opt.add(Implies(meet_kenneth, k_start >= KENNETH_START))
    opt.add(Implies(meet_kenneth, k_end <= KENNETH_END))
    opt.add(Implies(meet_kenneth, k_end - k_start >= MIN_MEET_KENNETH))
    # Must travel from Fisherman's Wharf to Nob Hill before meeting start
    opt.add(Implies(meet_kenneth, k_start >= arrive_FW + FW_to_NH))
    opt.add(Implies(meet_kenneth, k_end >= k_start))

    # If not meeting, pin times to 0 to avoid spurious optimization
    opt.add(Implies(Not(meet_kenneth), And(k_start == 0, k_end == 0)))

    # Objectives: maximize number of friends met, then maximize total meeting time
    num_meets = If(meet_kenneth, 1, 0)
    total_meet_time = If(meet_kenneth, k_end - k_start, 0)

    opt.maximize(num_meets)
    opt.maximize(total_meet_time)

    if opt.check() != sat:
        return {"itinerary": []}

    m = opt.model()

    itinerary = []
    if is_true(m.evaluate(meet_kenneth, model_completion=True)):
        ks = m.evaluate(k_start, model_completion=True).as_long()
        ke = m.evaluate(k_end, model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": minutes_to_hhmm(ks),
            "end_time": minutes_to_hhmm(ke),
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, separators=(",", ":")))