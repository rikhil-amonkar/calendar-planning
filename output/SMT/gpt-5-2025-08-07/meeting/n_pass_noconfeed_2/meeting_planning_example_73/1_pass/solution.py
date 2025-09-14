import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, Sum, sat

def parse_time(tstr):
    # Expects 'H:MM' or 'HH:MM'
    parts = tstr.strip().split(':')
    h = int(parts[0])
    m = int(parts[1])
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Input parameters (can be modified as variables)
    locations = ["Russian Hill", "Pacific Heights"]
    travel_minutes = {
        ("Russian Hill", "Pacific Heights"): 7,
        ("Pacific Heights", "Russian Hill"): 7,
    }

    arrival_location = "Russian Hill"
    arrival_time_str = "9:00"  # arrival at Russian Hill
    arrival_time = parse_time(arrival_time_str)

    people = [
        {
            "name": "Barbara",
            "location": "Pacific Heights",
            "available_start": "7:15",
            "available_end": "22:00",
            "min_meet_minutes": 60,
        }
    ]

    def travel_time(a, b):
        return travel_minutes.get((a, b), None)

    # Z3 Optimize model
    opt = Optimize()
    opt.set(priority='lex')

    # Decision variables per person
    person_vars = []
    for p in people:
        name = p["name"]
        loc = p["location"]
        av_start = parse_time(p["available_start"])
        av_end = parse_time(p["available_end"])
        min_meet = p["min_meet_minutes"]

        meet = Bool(f"meet_{name}")
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")

        person_vars.append({
            "name": name,
            "location": loc,
            "available_start": av_start,
            "available_end": av_end,
            "min_meet": min_meet,
            "meet": meet,
            "start": start,
            "end": end
        })

        # Bounds for time variables
        opt.add(start >= 0, start <= 24 * 60)
        opt.add(end >= 0, end <= 24 * 60)

        # If meeting, must respect availability and travel from arrival location
        tt = travel_time(arrival_location, loc)
        if tt is None:
            # If no travel time defined, cannot meet
            opt.add(Implies(meet, False))
            tt = 10**6  # dummy
        earliest_arrival_at_loc = arrival_time + tt

        opt.add(Implies(meet, And(
            start >= earliest_arrival_at_loc,
            start >= av_start,
            end <= av_end,
            end >= start + min_meet,
        )))
        # If not meeting, pin times to 0 to avoid spurious values
        opt.add(Implies(Not(meet), And(start == 0, end == 0)))

    # No overlap constraints for multiple meetings (not needed with one person).
    # If extended to multiple friends, add sequencing and travel-time-between-meetings constraints.

    # Objectives:
    # 1) Maximize number of meetings
    total_meets = Sum([If(v["meet"], 1, 0) for v in person_vars])
    opt.maximize(total_meets)

    # 2) Maximize total meeting time
    total_minutes = Sum([If(v["meet"], v["end"] - v["start"], 0) for v in person_vars])
    opt.maximize(total_minutes)

    # 3) Minimize earliest start time among scheduled meetings (start earlier in case of ties)
    # Compute min start over meetings; if none meet, default 24*60
    # Use an auxiliary variable to represent earliest start
    if person_vars:
        earliest_start = Int("earliest_start")
        opt.add(earliest_start >= 0, earliest_start <= 24 * 60)
        # Constrain earliest_start to be the minimum start among those actually met
        # earliest_start = min_i If(meet_i, start_i, 24*60)
        # Implement via constraints: earliest_start <= each candidate, and equality to one candidate if any meet.
        candidates = [If(v["meet"], v["start"], 24 * 60) for v in person_vars]
        for c in candidates:
            opt.add(earliest_start <= c)
        # If at least one meeting, ensure earliest_start equals one of the actual starts
        if len(person_vars) == 1:
            v = person_vars[0]
            opt.add(Implies(v["meet"], earliest_start == v["start"]))
            opt.add(Implies(Not(v["meet"]), earliest_start == 24 * 60))
        else:
            # For generality (not used here with one person)
            at_least_one = Or([v["meet"] for v in person_vars])
            opt.add(Implies(Not(at_least_one), earliest_start == 24 * 60))
            # If at least one, force equality to some candidate
            opt.add(Implies(at_least_one, Or([earliest_start == If(v["meet"], v["start"], 24 * 60) for v in person_vars])))
        # Minimize earliest start (lex objective 3)
        opt.minimize(earliest_start)

    # Solve
    result = opt.check()
    itinerary = []

    if result == sat:
        model = opt.model()
        # Collect scheduled meetings
        scheduled = []
        for v in person_vars:
            if model.eval(v["meet"], model_completion=True):
                start_min = model.eval(v["start"]).as_long()
                end_min = model.eval(v["end"]).as_long()
                scheduled.append({
                    "person": v["name"],
                    "location": v["location"],
                    "start_min": start_min,
                    "end_min": end_min
                })

        # Sort by start time
        scheduled.sort(key=lambda x: x["start_min"])

        for item in scheduled:
            itinerary.append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": minutes_to_str(item["start_min"]),
                "end_time": minutes_to_str(item["end_min"])
            })
    else:
        itinerary = []

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()