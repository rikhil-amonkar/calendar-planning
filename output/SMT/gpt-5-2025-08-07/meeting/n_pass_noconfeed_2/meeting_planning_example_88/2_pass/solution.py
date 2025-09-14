import json
from z3 import Optimize, Int, Bool, If, Implies, And, Or, Not, Sum, sat, is_true

def time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Input parameters
    start_location = "Sunset District"
    arrival_at_start_location = 9 * 60  # 9:00 in minutes
    travel_times = {
        ("Sunset District", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Sunset District"): 10
    }

    friends = [
        {
            "name": "Joshua",
            "location": "Golden Gate Park",
            "avail_start": 20 * 60 + 45,  # 20:45
            "avail_end": 21 * 60 + 45,    # 21:45
            "min_meeting": 15
        }
    ]

    # Z3 optimization model
    opt = Optimize()
    opt.set(priority='lex')

    # Variables per friend
    friend_vars = []
    for i, f in enumerate(friends):
        meet = Bool(f"meet_{i}")
        depart = Int(f"depart_{i}")   # departure time from start location (minutes)
        arrive = Int(f"arrive_{i}")   # arrival time at friend's location
        start = Int(f"start_{i}")     # meeting start
        end = Int(f"end_{i}")         # meeting end
        duration = Int(f"duration_{i}")
        wait = Int(f"wait_{i}")       # waiting time at location before meeting start

        # General bounds
        day_end = 24 * 60
        for var in [depart, arrive, start, end, duration, wait]:
            opt.add(var >= 0, var <= day_end)

        # Travel time from start location to friend's location
        tkey = (start_location, f["location"])
        if tkey not in travel_times:
            # If no travel time defined, meeting is impossible
            opt.add(meet == False)
            travel_time = 0
        else:
            travel_time = travel_times[tkey]

        # Constraints if we decide to meet this friend
        opt.add(Implies(meet, depart >= arrival_at_start_location))
        opt.add(Implies(meet, arrive == depart + travel_time))
        opt.add(Implies(meet, start >= arrive))
        opt.add(Implies(meet, start >= f["avail_start"]))
        opt.add(Implies(meet, end <= f["avail_end"]))
        opt.add(Implies(meet, end > start))
        opt.add(Implies(meet, duration == end - start))
        opt.add(Implies(meet, duration >= f["min_meeting"]))
        opt.add(Implies(meet, wait == start - arrive))
        # Non-negativity for wait and duration already ensured by bounds; tighten under meet:
        opt.add(Implies(meet, And(wait >= 0, duration >= 0)))

        # If not meeting, set duration and wait to 0 to keep model tight (optional)
        opt.add(Implies(Not(meet), And(duration == 0, wait == 0)))

        friend_vars.append({
            "meet": meet, "depart": depart, "arrive": arrive,
            "start": start, "end": end, "duration": duration, "wait": wait,
            "data": f
        })

    # Objective 1: Maximize number of friends met
    meet_count = Sum([If(v["meet"], 1, 0) for v in friend_vars])
    opt.maximize(meet_count)

    # Objective 2: Maximize total meeting duration
    total_duration = Sum([If(v["meet"], v["duration"], 0) for v in friend_vars])
    opt.maximize(total_duration)

    # Objective 3: Minimize total waiting time at locations before meetings (prefer just-in-time arrival)
    total_wait = Sum([If(v["meet"], v["wait"], 0) for v in friend_vars])
    opt.minimize(total_wait)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result, indent=2))
        return

    model = opt.model()

    # Build itinerary
    itinerary = []
    for v in friend_vars:
        if is_true(model.eval(v["meet"], model_completion=True)):
            start_m = model.eval(v["start"], model_completion=True).as_long()
            end_m = model.eval(v["end"], model_completion=True).as_long()
            entry = {
                "action": "meet",
                "location": v["data"]["location"],
                "person": v["data"]["name"],
                "start_time": time_str(start_m),
                "end_time": time_str(end_m)
            }
            itinerary.append(entry)

    # Sort itinerary by start_time
    itinerary.sort(key=lambda e: int(e["start_time"].split(":")[0]) * 60 + int(e["start_time"].split(":")[1]))

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()