import json
from z3 import Int, Bool, Optimize, If, And, Or, Not, Sum

def time_to_minutes(tstr):
    # tstr like "9:00" or "14:15"
    parts = tstr.strip().split(":")
    h = int(parts[0])
    m = int(parts[1])
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Input parameters (as variables)
    locations = ["Fisherman's Wharf", "Nob Hill"]
    travel_minutes = {
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Nob Hill", "Fisherman's Wharf"): 11,
    }
    arrival_location = "Fisherman's Wharf"
    arrival_time_str = "9:00"

    friends = [
        {
            "name": "Kenneth",
            "location": "Nob Hill",
            "available_start": "14:15",
            "available_end": "19:45",
            "min_duration": 90
        }
    ]

    # Prepare constants
    DAY_START = 0
    DAY_END = 24 * 60

    arrival_time = time_to_minutes(arrival_time_str)

    # Z3 model
    opt = Optimize()

    friend_vars = []
    total_meet_count_terms = []
    total_meeting_minutes_terms = []

    for f in friends:
        name = f["name"]
        loc = f["location"]
        avail_s = time_to_minutes(f["available_start"])
        avail_e = time_to_minutes(f["available_end"])
        min_dur = f["min_duration"]

        # Decision variables
        s = Int(f"s_{name}")
        e = Int(f"e_{name}")
        meet = Bool(f"meet_{name}")

        # Bounds
        opt.add(And(s >= DAY_START, s <= DAY_END))
        opt.add(And(e >= DAY_START, e <= DAY_END))

        # Travel feasibility from arrival
        travel_to_meet = travel_minutes.get((arrival_location, loc), 0)
        earliest_reachable = arrival_time + travel_to_meet

        # If meeting, enforce timing constraints
        opt.add(
            If(
                meet,
                And(
                    s >= avail_s,
                    s >= earliest_reachable,
                    e <= avail_e,
                    e - s >= min_dur
                ),
                And(
                    # If not meeting, keep s,e within day; no additional constraints
                    s >= DAY_START,
                    e >= s,  # ensure non-negative interval
                    e <= DAY_END
                )
            )
        )

        meet_int = If(meet, 1, 0)
        dur_int = If(meet, e - s, 0)
        total_meet_count_terms.append(meet_int)
        total_meeting_minutes_terms.append(dur_int)

        friend_vars.append({
            "friend": f,
            "vars": {"s": s, "e": e, "meet": meet},
            "derived": {"earliest_reachable": earliest_reachable}
        })

    # Objectives:
    # 1) Maximize number of friends met
    # 2) Maximize total meeting time
    total_meet_count = Sum(total_meet_count_terms) if total_meet_count_terms else Int("zero_meets")
    if not total_meet_count_terms:
        opt.add(total_meet_count == 0)
    total_meeting_minutes = Sum(total_meeting_minutes_terms) if total_meeting_minutes_terms else Int("zero_minutes")
    if not total_meeting_minutes_terms:
        opt.add(total_meeting_minutes == 0)

    h1 = opt.maximize(total_meet_count)
    h2 = opt.maximize(total_meeting_minutes)

    if opt.check() != sat:
        # No feasible schedule
        result = {"itinerary": []}
        print(json.dumps(result, ensure_ascii=False))
        return

    model = opt.model()

    itinerary = []
    for fv in friend_vars:
        f = fv["friend"]
        v = fv["vars"]
        meet_val = model.eval(v["meet"])
        if str(meet_val) == "True":
            s_min = model.eval(v["s"]).as_long()
            e_min = model.eval(v["e"]).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": minutes_to_time(s_min),
                "end_time": minutes_to_time(e_min)
            })

    # Sort itinerary by start_time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()