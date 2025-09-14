import json
from z3 import Optimize, Int, Bool, And, If, Implies, Sum, sat

def parse_time_24h(s):
    # expects 'H:MM' in 24-hour format
    h, m = s.split(':')
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Input parameters (24-hour format as required)
    config = {
        "start_location": "Golden Gate Park",
        "arrival_time": "9:00",
        "people": [
            {
                "name": "David",
                "location": "Chinatown",
                "available_start": "16:00",
                "available_end": "21:45",
                "min_meet_minutes": 105
            }
        ],
        "travel_minutes": {
            ("Golden Gate Park", "Chinatown"): 23,
            ("Chinatown", "Golden Gate Park"): 23
        }
    }

    # Convert times to minutes
    arrival_time_min = parse_time_24h(config["arrival_time"])

    # Z3 model
    opt = Optimize()

    meet_vars = []
    for person in config["people"]:
        name = person["name"]
        loc = person["location"]
        avail_start = parse_time_24h(person["available_start"])
        avail_end = parse_time_24h(person["available_end"])
        min_meet = person["min_meet_minutes"]

        s = Int(f"{name}_start")
        e = Int(f"{name}_end")
        meet = Bool(f"meet_{name}")

        # Travel from start location to person's location
        travel_from_start = config["travel_minutes"].get((config["start_location"], loc), None)
        if travel_from_start is None:
            # If no travel time is provided, disallow meeting
            opt.add(meet == False)
            travel_from_start = 0  # dummy to avoid None uses

        # Basic domain constraints
        opt.add(Implies(meet, And(
            s >= 0, e >= 0, s < 24 * 60, e <= 24 * 60,
            s >= avail_start,
            e <= avail_end,
            e > s,
            (e - s) >= min_meet,
            s >= arrival_time_min + travel_from_start
        )))
        # If not meeting, set a safe default for s/e (not required, but keeps model tidy)
        opt.add(Implies(And(meet == False), And(s == 0, e == 0)))

        meet_vars.append({
            "name": name,
            "location": loc,
            "meet": meet,
            "start": s,
            "end": e
        })

    # Objectives:
    # 1) Maximize number of friends met
    num_met = Sum([If(v["meet"], 1, 0) for v in meet_vars])
    opt.maximize(num_met)

    # 2) Maximize total meeting duration
    total_duration = Sum([If(v["meet"], v["end"] - v["start"], 0) for v in meet_vars])
    opt.maximize(total_duration)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Build itinerary JSON
    itinerary = []
    for v in meet_vars:
        if model.evaluate(v["meet"], model_completion=True):
            s_val = model.evaluate(v["start"], model_completion=True).as_long()
            e_val = model.evaluate(v["end"], model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": v["location"],
                "person": v["name"],
                "start_time": fmt_time(s_val),
                "end_time": fmt_time(e_val)
            })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()