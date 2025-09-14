import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat, is_true

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Input parameters
    day_start_location = "The Castro"
    day_start_time = 9 * 60  # 9:00 AM in minutes

    # Travel times (minutes)
    travel = {
        "The Castro": {"Alamo Square": 8, "Union Square": 19, "Chinatown": 20},
        "Alamo Square": {"The Castro": 8, "Union Square": 14, "Chinatown": 16},
        "Union Square": {"The Castro": 19, "Alamo Square": 15, "Chinatown": 7},
        "Chinatown": {"The Castro": 22, "Alamo Square": 17, "Union Square": 7},
    }

    # Friends constraints
    friends = {
        "Emily": {
            "location": "Alamo Square",
            "window_start": 11 * 60 + 45,  # 11:45
            "window_end": 15 * 60 + 15,    # 15:15
            "min_duration": 105,           # 1h45m
        },
        "Barbara": {
            "location": "Union Square",
            "window_start": 16 * 60 + 45,  # 16:45
            "window_end": 18 * 60 + 15,    # 18:15
            "min_duration": 60,            # 1h
        },
        "William": {
            "location": "Chinatown",
            "window_start": 17 * 60 + 15,  # 17:15
            "window_end": 19 * 60,         # 19:00
            "min_duration": 105,           # 1h45m
        },
    }

    # Z3 setup
    opt = Optimize()
    opt.set(priority='lex')  # Lexicographic optimization: max #met, then max total meeting time

    people = list(friends.keys())

    meet = {p: Bool(f"meet_{p}") for p in people}
    start = {p: Int(f"start_{p}") for p in people}
    end = {p: Int(f"end_{p}") for p in people}
    dur = {p: Int(f"dur_{p}") for p in people}

    # General bounds and per-person constraints
    for p in people:
        loc = friends[p]["location"]
        ws = friends[p]["window_start"]
        we = friends[p]["window_end"]
        md = friends[p]["min_duration"]

        # Bounds
        opt.add(And(start[p] >= 0, start[p] <= 24 * 60))
        opt.add(And(end[p] >= 0, end[p] <= 24 * 60))
        opt.add(dur[p] == end[p] - start[p])

        # If meeting, enforce within window, min duration, and feasible from day start (travel from The Castro)
        # If not meeting, force zero-length and zero times for determinism
        opt.add(
            If(
                meet[p],
                And(
                    start[p] >= ws,
                    end[p] <= we,
                    dur[p] >= md,
                    start[p] >= day_start_time + travel[day_start_location][loc]
                ),
                And(start[p] == 0, end[p] == 0, dur[p] == 0)
            )
        )

    # Non-overlap with travel time between meetings
    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            pi, pj = people[i], people[j]
            li, lj = friends[pi]["location"], friends[pj]["location"]
            tij = travel[li][lj]
            tji = travel[lj][li]

            # If both meetings happen, enforce ordering with travel time.
            # Otherwise, no constraint.
            opt.add(
                Or(
                    Not(And(meet[pi], meet[pj])),
                    And(meet[pi], meet[pj], end[pi] + tij <= start[pj]),
                    And(meet[pi], meet[pj], end[pj] + tji <= start[pi])
                )
            )

    # Objectives
    total_met = Sum([If(meet[p], 1, 0) for p in people])
    total_meeting_time = Sum([dur[p] for p in people])

    opt.maximize(total_met)
    opt.maximize(total_meeting_time)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Build itinerary
    entries = []
    for p in people:
        if is_true(model.evaluate(meet[p])):
            s = model.evaluate(start[p]).as_long()
            e = model.evaluate(end[p]).as_long()
            entries.append({
                "action": "meet",
                "location": friends[p]["location"],
                "person": p,
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e),
            })

    # Sort by start time
    entries.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    output = {"itinerary": entries}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()