import json
from z3 import Optimize, Int, And, sat

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Parameters (input variables)
    arrival_location = "Golden Gate Park"
    start_at_ggp = 9 * 60  # 9:00 -> 540 minutes
    travel_ggp_to_chinatown = 23
    travel_chinatown_to_ggp = 23  # symmetrical, provided for completeness

    # Friend David's availability
    person = "David"
    meet_location = "Chinatown"
    david_available_start = 16 * 60        # 16:00 -> 960
    david_available_end = 21 * 60 + 45     # 21:45 -> 1305
    min_meet_minutes = 105

    # Decision variables
    opt = Optimize()
    depart_time = Int("depart_time")  # time leaving GGP
    start_time = Int("start_time")    # meeting start in Chinatown
    end_time = Int("end_time")        # meeting end in Chinatown
    meet_duration = Int("meet_duration")

    # Constraints
    # Can't depart before arrival at GGP
    opt.add(depart_time >= start_at_ggp)

    # Travel and meeting linkage: arrive exactly at meeting start
    opt.add(start_time == depart_time + travel_ggp_to_chinatown)

    # Meeting must be within David's availability
    opt.add(start_time >= david_available_start)
    opt.add(end_time <= david_available_end)
    opt.add(end_time > start_time)

    # Duration handling
    opt.add(meet_duration == end_time - start_time)
    opt.add(meet_duration >= min_meet_minutes)

    # Keep all times within the same day (0..1439)
    opt.add(And(depart_time >= 0, depart_time <= 23*60 + 59))
    opt.add(And(start_time >= 0, start_time <= 23*60 + 59))
    opt.add(And(end_time >= 0, end_time <= 23*60 + 59))

    # Objectives:
    # 1) Maximize time spent meeting David
    # 2) Maximize depart_time to avoid arriving early (given 1), ensures minimal waiting
    opt.maximize(meet_duration)
    opt.maximize(depart_time)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()
    s_time = model[start_time].as_long()
    e_time = model[end_time].as_long()

    itinerary = [
        {
            "action": "meet",
            "location": meet_location,
            "person": person,
            "start_time": minutes_to_str(s_time),
            "end_time": minutes_to_str(e_time)
        }
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()