# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def minutes(hh, mm):
    return hh * 60 + mm

def to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def solve():
    # Constants
    FD = "Financial District"
    CH = "Chinatown"
    GGP = "Golden Gate Park"

    # Travel times (minutes), directional where specified
    T = {
        (FD, CH): 5,
        (FD, GGP): 23,
        (CH, FD): 5,
        (CH, GGP): 23,
        (GGP, FD): 26,
        (GGP, CH): 23,
    }

    # Start at FD at 09:00
    start_loc = FD
    arrival_time = minutes(9, 0)  # 540

    # Friends data: location, availability [start, end], min_duration
    friends = {
        "Kenneth": {
            "loc": CH,
            "avail_start": minutes(12, 0),
            "avail_end": minutes(15, 0),
            "min_dur": 90
        },
        "Barbara": {
            "loc": GGP,
            "avail_start": minutes(8, 15),
            "avail_end": minutes(19, 0),
            "min_dur": 45
        }
    }

    # Create Z3 Optimize model
    opt = Optimize()

    # Decision variables per friend
    meet = {name: Bool(f"meet_{name}") for name in friends}
    start = {name: Int(f"start_{name}") for name in friends}
    end = {name: Int(f"end_{name}") for name in friends}
    dur = {name: Int(f"dur_{name}") for name in friends}

    # Bounds and base constraints
    for name, info in friends.items():
        opt.add(start[name] >= 0, start[name] <= 24*60)
        opt.add(end[name] >= 0, end[name] <= 24*60)
        opt.add(dur[name] >= 0, dur[name] <= 24*60)
        opt.add(end[name] == start[name] + dur[name])

        # If we meet, must respect availability and min duration
        opt.add(Implies(meet[name], start[name] >= info["avail_start"]))
        opt.add(Implies(meet[name], end[name] <= info["avail_end"]))
        opt.add(Implies(meet[name], dur[name] >= info["min_dur"]))

        # If we don't meet, zero duration
        opt.add(Implies(Not(meet[name]), dur[name] == 0))

    # Order variable: does Barbara happen before Kenneth if both met?
    b_before_k = Bool("b_before_k")

    # Arrival times from starting location
    arr_to = {
        "Kenneth": arrival_time + T[(start_loc, friends["Kenneth"]["loc"])],
        "Barbara": arrival_time + T[(start_loc, friends["Barbara"]["loc"])]
    }

    # Travel times between friends
    travel_B_to_K = T[(friends["Barbara"]["loc"], friends["Kenneth"]["loc"])]
    travel_K_to_B = T[(friends["Kenneth"]["loc"], friends["Barbara"]["loc"])]

    # Precedence and travel feasibility constraints
    # If only one meeting, ensure we can arrive from the start
    opt.add(Implies(And(meet["Barbara"], Not(meet["Kenneth"])), start["Barbara"] >= arr_to["Barbara"]))
    opt.add(Implies(And(meet["Kenneth"], Not(meet["Barbara"])), start["Kenneth"] >= arr_to["Kenneth"]))

    # If both meetings, enforce order and travel between
    opt.add(Implies(And(meet["Barbara"], meet["Kenneth"], b_before_k),
                    And(start["Barbara"] >= arr_to["Barbara"],
                        start["Kenneth"] >= end["Barbara"] + travel_B_to_K)))
    opt.add(Implies(And(meet["Barbara"], meet["Kenneth"], Not(b_before_k)),
                    And(start["Kenneth"] >= arr_to["Kenneth"],
                        start["Barbara"] >= end["Kenneth"] + travel_K_to_B)))

    # Objective 1: maximize number of friends met
    n_met = Sum([If(meet[name], 1, 0) for name in friends])
    opt.maximize(n_met)

    # Define finish time (end of last meeting)
    # If both: last depends on order; else whichever is met; if none: finish = arrival_time
    finish_time = If(And(meet["Barbara"], meet["Kenneth"]),
                     If(b_before_k, end["Kenneth"], end["Barbara"]),
                     If(meet["Barbara"], end["Barbara"],
                        If(meet["Kenneth"], end["Kenneth"], arrival_time)))
    opt.minimize(finish_time)

    # Objective 3: minimize total waiting (idle) time (before first meeting + between meetings)
    wait_first = If(And(meet["Barbara"], meet["Kenneth"], b_before_k),
                    start["Barbara"] - arr_to["Barbara"],
                    If(And(meet["Barbara"], meet["Kenneth"], Not(b_before_k)),
                       start["Kenneth"] - arr_to["Kenneth"],
                       If(And(meet["Barbara"], Not(meet["Kenneth"])),
                          start["Barbara"] - arr_to["Barbara"],
                          If(And(meet["Kenneth"], Not(meet["Barbara"])),
                             start["Kenneth"] - arr_to["Kenneth"], 0))))
    wait_between = If(And(meet["Barbara"], meet["Kenneth"], b_before_k),
                      start["Kenneth"] - (end["Barbara"] + travel_B_to_K),
                      If(And(meet["Barbara"], meet["Kenneth"], Not(b_before_k)),
                         start["Barbara"] - (end["Kenneth"] + travel_K_to_B), 0))
    opt.add(wait_first >= 0, wait_between >= 0)
    opt.minimize(wait_first + wait_between)

    # Solve
    if opt.check() != sat:
        raise RuntimeError("No feasible itinerary found")

    m = opt.model()

    # Build itinerary
    entries = []
    for person in ["Barbara", "Kenneth"]:
        if m.evaluate(meet[person]):
            s = m.evaluate(start[person]).as_long()
            e = m.evaluate(end[person]).as_long()
            entries.append((s, {
                "action": "meet",
                "person": person,
                "start_time": to_hhmm(s),
                "end_time": to_hhmm(e)
            }))

    # Sort by start time
    entries.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in entries]

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    solve()