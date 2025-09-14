import json
from z3 import *

def t(h, m):
    return h * 60 + m

def min_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    Sunset = "Sunset District"
    Chinatown = "Chinatown"
    RussianHill = "Russian Hill"
    NorthBeach = "North Beach"

    # Travel times (in minutes), possibly asymmetric
    travel = {
        Sunset: {Chinatown: 30, RussianHill: 24, NorthBeach: 29},
        Chinatown: {Sunset: 29, RussianHill: 7, NorthBeach: 3},
        RussianHill: {Sunset: 23, Chinatown: 9, NorthBeach: 5},
        NorthBeach: {Sunset: 27, Chinatown: 6, RussianHill: 4},
    }

    # Arrival at Sunset at 9:00
    arrival_time = t(9, 0)

    # Friends' availability windows and minimum meeting durations
    friends = {
        "Anthony": {
            "location": Chinatown,
            "window_start": t(13, 15),
            "window_end": t(14, 30),
            "min_duration": 60,
        },
        "Rebecca": {
            "location": RussianHill,
            "window_start": t(19, 30),
            "window_end": t(21, 15),
            "min_duration": 105,
        },
        "Melissa": {
            "location": NorthBeach,
            "window_start": t(8, 15),
            "window_end": t(13, 30),
            "min_duration": 105,
        },
    }

    # Z3 variables
    s = {name: Int(f"s_{name}") for name in friends}  # start times
    e = {name: Int(f"e_{name}") for name in friends}  # end times
    meet = {name: Bool(f"meet_{name}") for name in friends}

    # Pairwise ordering variables (who comes before whom if both are met)
    names = list(friends.keys())
    before = {}  # before[(a,b)] = Bool that a is before b
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            a, b = names[i], names[j]
            before[(a, b)] = Bool(f"{a}_before_{b}")
            before[(b, a)] = Bool(f"{b}_before_{a}")

    opt = Optimize()

    # Constraints: meeting windows, durations, initial reachability from Sunset
    for name, info in friends.items():
        loc = info["location"]
        ws = info["window_start"]
        we = info["window_end"]
        dmin = info["min_duration"]

        # If meeting, times within window
        opt.add(Implies(meet[name], And(
            s[name] >= ws,
            e[name] <= we,
            e[name] - s[name] >= dmin,
            s[name] >= arrival_time + travel[Sunset][loc],  # must be reachable from initial location
            e[name] > s[name]
        )))
        # If not meeting, no constraints on s/e, but they are integers implicitly

    # Pairwise ordering and travel-time feasibility
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            a, b = names[i], names[j]
            loc_a = friends[a]["location"]
            loc_b = friends[b]["location"]
            a_before_b = before[(a, b)]
            b_before_a = before[(b, a)]

            # Ordering booleans only relevant if both are met
            opt.add(Implies(And(meet[a], meet[b]), Xor(a_before_b, b_before_a)))
            opt.add(Implies(Not(And(meet[a], meet[b])), And(Not(a_before_b), Not(b_before_a))))

            # Travel constraints
            opt.add(Implies(a_before_b, s[b] >= e[a] + travel[loc_a][loc_b]))
            opt.add(Implies(b_before_a, s[a] >= e[b] + travel[loc_b][loc_a]))

    # Objective: maximize number of friends met
    meet_count = Sum([If(meet[name], IntVal(1), IntVal(0)) for name in names])
    h1 = opt.maximize(meet_count)

    # Tiebreaker objective: minimize the latest end time (makespan)
    latest_end = max(
        # If not meeting someone, fallback to arrival_time so it doesn't dominate max
        If(meet[name], e[name], IntVal(arrival_time))
        for name in names
    )
    h2 = opt.minimize(latest_end)

    # Optionally, minimize total meeting start times to prefer earlier schedules (secondary tiebreaker)
    total_start = Sum([If(meet[name], s[name], IntVal(0)) for name in names])
    h3 = opt.minimize(total_start)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    itinerary = []
    for name in names:
        if is_true(model[meet[name]]):
            start = model[s[name]].as_long()
            end = model[e[name]].as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[name]["location"],
                "person": name,
                "start_time": min_to_str(start),
                "end_time": min_to_str(end),
            })

    # Sort by start time for readability
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()