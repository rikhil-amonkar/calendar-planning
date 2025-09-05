import json
from z3 import Int, If, Optimize, sat

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def solve_schedule():
    # Input parameters (in minutes)
    # Travel times
    travel_AS_to_RD = 12
    travel_RD_to_AS = 13  # given, not required for the single meeting but kept for completeness

    # You arrive at Alamo Square at 9:00
    arrive_AS_time = 9 * 60  # 540

    # Timothy's availability at Richmond District: 20:45 to 21:30
    timothy_start = 20 * 60 + 45  # 1245
    timothy_end = 21 * 60 + 30    # 1290

    # Minimum desired meeting duration (minutes)
    min_meeting_minutes = 45

    def build_and_solve(require_min=True):
        o = Optimize()

        # Decision variables
        depart_AS_to_RD = Int("depart_AS_to_RD")  # departure time from AS to RD
        arrive_RD = Int("arrive_RD")              # arrival time at RD
        meet_start = Int("meet_start")            # chosen meeting start time
        meet_end = Int("meet_end")                # chosen meeting end time
        meet_len = Int("meet_len")                # meeting duration

        # Core constraints
        o.add(depart_AS_to_RD >= arrive_AS_time)       # cannot depart before arriving at AS
        o.add(depart_AS_to_RD <= 23 * 60)              # same day bound
        o.add(arrive_RD == depart_AS_to_RD + travel_AS_to_RD)

        # Meeting must occur within both our presence and Timothy's window
        # meet_start is the later of arrival or Timothy's start
        o.add(meet_start == If(arrive_RD >= timothy_start, arrive_RD, timothy_start))
        # We plan to meet until Timothy's end (maximize duration)
        o.add(meet_end == timothy_end)

        # Duration computation
        o.add(meet_len == meet_end - meet_start)
        o.add(meet_start < meet_end)

        # Minimum desired meeting constraint (hard if require_min=True)
        if require_min:
            o.add(meet_len >= min_meeting_minutes)
        else:
            o.add(meet_len >= 0)

        # Objectives:
        # 1) Maximize total meeting minutes
        o.maximize(meet_len)
        # 2) Arrive as late as possible (reduces waiting) while keeping optimal meeting time
        o.maximize(arrive_RD)
        # 3) Optionally minimize departure time variability (not strictly necessary)

        result = o.check()
        if result != sat:
            return None

        m = o.model()
        return {
            "depart_AS_to_RD": m.eval(depart_AS_to_RD).as_long(),
            "arrive_RD": m.eval(arrive_RD).as_long(),
            "meet_start": m.eval(meet_start).as_long(),
            "meet_end": m.eval(meet_end).as_long(),
            "meet_len": m.eval(meet_len).as_long(),
        }

    # Try with the minimum meeting requirement as a hard constraint
    sol = build_and_solve(require_min=True)
    # If not satisfiable, relax the minimum and maximize what we can meet
    if sol is None:
        sol = build_and_solve(require_min=False)

    itinerary = []
    if sol is not None and sol["meet_len"] > 0:
        itinerary.append({
            "action": "meet",
            "location": "Richmond District",
            "person": "Timothy",
            "start_time": minutes_to_str(sol["meet_start"]),
            "end_time": minutes_to_str(sol["meet_end"])
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_schedule()