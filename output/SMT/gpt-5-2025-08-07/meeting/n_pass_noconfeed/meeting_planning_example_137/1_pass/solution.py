import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    FD = "Financial District"
    CH = "Chinatown"
    GG = "Golden Gate Park"

    # Travel times in minutes (asymmetric where specified)
    travel = {
        (FD, CH): 5,
        (CH, FD): 5,
        (FD, GG): 23,
        (CH, GG): 23,
        (GG, CH): 23,
        (GG, FD): 26,
    }

    # Arrival info
    arrive_loc = FD
    arrive_time = 9 * 60  # 9:00 -> 540 minutes

    # Friends availability and minimum meeting times
    friends = {
        "Kenneth": {
            "location": CH,
            "avail_start": 12 * 60,     # 12:00 -> 720
            "avail_end": 15 * 60,       # 15:00 -> 900
            "min_meet": 90
        },
        "Barbara": {
            "location": GG,
            "avail_start": 8 * 60 + 15, # 8:15 -> 495
            "avail_end": 19 * 60,       # 19:00 -> 1140
            "min_meet": 45
        }
    }

    # Z3 variables
    s = Optimize()
    s.set(priority='lex')

    # Meeting variables
    meet_K = Bool("meet_K")
    start_K = Int("start_K")
    end_K = Int("end_K")

    meet_B = Bool("meet_B")
    start_B = Int("start_B")
    end_B = Int("end_B")

    # Order variable: True means B before K, False means K before B
    B_before_K = Bool("B_before_K")

    # Bounds for time variables (0 - 24:00)
    for v in [start_K, end_K, start_B, end_B]:
        s.add(v >= 0, v <= 24 * 60)

    # Availability and duration constraints
    # Kenneth (Chinatown: 12:00-15:00, min 90)
    s.add(Implies(meet_K, And(
        start_K >= friends["Kenneth"]["avail_start"],
        end_K <= friends["Kenneth"]["avail_end"],
        end_K - start_K >= friends["Kenneth"]["min_meet"],
        end_K > start_K
    )))

    # Barbara (Golden Gate Park: 8:15-19:00, min 45)
    s.add(Implies(meet_B, And(
        start_B >= friends["Barbara"]["avail_start"],
        end_B <= friends["Barbara"]["avail_end"],
        end_B - start_B >= friends["Barbara"]["min_meet"],
        end_B > start_B
    )))

    # Travel and sequencing constraints
    # If only Kenneth is met
    s.add(Implies(And(meet_K, Not(meet_B)), start_K >= arrive_time + travel[(arrive_loc, CH)]))
    # If only Barbara is met
    s.add(Implies(And(meet_B, Not(meet_K)), start_B >= arrive_time + travel[(arrive_loc, GG)]))

    # If both are met and Barbara is first
    s.add(Implies(And(meet_B, meet_K, B_before_K), And(
        start_B >= arrive_time + travel[(arrive_loc, GG)],
        start_K >= end_B + travel[(GG, CH)]
    )))

    # If both are met and Kenneth is first
    s.add(Implies(And(meet_B, meet_K, Not(B_before_K)), And(
        start_K >= arrive_time + travel[(arrive_loc, CH)],
        start_B >= end_K + travel[(CH, GG)]
    )))

    # Objective: maximize number of friends met, then maximize total meeting time
    meet_count = Int("meet_count")
    total_meeting = Int("total_meeting")

    s.add(meet_count == If(meet_B, 1, 0) + If(meet_K, 1, 0))
    s.add(total_meeting == If(meet_B, end_B - start_B, 0) + If(meet_K, end_K - start_K, 0))

    s.maximize(meet_count)
    s.maximize(total_meeting)

    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    schedule = []

    # Extract Kenneth meeting if scheduled
    if is_true(m.evaluate(meet_K)):
        k_start = m.evaluate(start_K).as_long()
        k_end = m.evaluate(end_K).as_long()
        schedule.append({
            "action": "meet",
            "location": CH,
            "person": "Kenneth",
            "start_time": minutes_to_str(k_start),
            "end_time": minutes_to_str(k_end)
        })

    # Extract Barbara meeting if scheduled
    if is_true(m.evaluate(meet_B)):
        b_start = m.evaluate(start_B).as_long()
        b_end = m.evaluate(end_B).as_long()
        schedule.append({
            "action": "meet",
            "location": GG,
            "person": "Barbara",
            "start_time": minutes_to_str(b_start),
            "end_time": minutes_to_str(b_end)
        })

    # Sort by start_time
    def parse_time_str(ts):
        h, mm = ts.split(":")
        return int(h) * 60 + int(mm)

    schedule.sort(key=lambda x: parse_time_str(x["start_time"]))

    print(json.dumps({"itinerary": schedule}))

if __name__ == "__main__":
    main()