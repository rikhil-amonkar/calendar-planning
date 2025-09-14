import json
from z3 import Int, Bool, If, Optimize, Or, And, Sum, sat, is_true

def minutes(h, m=0):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    locations = [
        "Sunset District",
        "Alamo Square",
        "Russian Hill",
        "Golden Gate Park",
        "Mission District",
    ]

    # Travel times in minutes (directed)
    travel = {
        "Sunset District": {
            "Alamo Square": 17,
            "Russian Hill": 24,
            "Golden Gate Park": 11,
            "Mission District": 24,
        },
        "Alamo Square": {
            "Sunset District": 16,
            "Russian Hill": 13,
            "Golden Gate Park": 9,
            "Mission District": 10,
        },
        "Russian Hill": {
            "Sunset District": 23,
            "Alamo Square": 15,
            "Golden Gate Park": 21,
            "Mission District": 16,
        },
        "Golden Gate Park": {
            "Sunset District": 10,
            "Alamo Square": 10,
            "Russian Hill": 19,
            "Mission District": 17,
        },
        "Mission District": {
            "Sunset District": 24,
            "Alamo Square": 11,
            "Russian Hill": 15,
            "Golden Gate Park": 17,
        },
    }

    # Friends constraints
    friends = {
        "Charles": {
            "location": "Alamo Square",
            "window_start": minutes(18, 0),
            "window_end": minutes(20, 45),
            "min_duration": 90,
        },
        "Margaret": {
            "location": "Russian Hill",
            "window_start": minutes(9, 0),
            "window_end": minutes(16, 0),
            "min_duration": 30,
        },
        "Daniel": {
            "location": "Golden Gate Park",
            "window_start": minutes(8, 0),
            "window_end": minutes(13, 30),
            "min_duration": 15,
        },
        "Stephanie": {
            "location": "Mission District",
            "window_start": minutes(20, 30),
            "window_end": minutes(22, 0),
            "min_duration": 90,
        },
    }

    start_location = "Sunset District"
    arrival_time = minutes(9, 0)

    opt = Optimize()
    opt.set(priority='lex')

    # Variables per friend
    s = {}        # start time in minutes
    dur = {}      # duration in minutes
    meet = {}     # whether to meet
    end_eff = {}  # effective end time (0 if not meeting)

    # Create variables and constraints
    for person, info in friends.items():
        s[person] = Int(f"s_{person}")
        dur[person] = Int(f"dur_{person}")
        meet[person] = Bool(f"meet_{person}")
        end_eff[person] = Int(f"end_eff_{person}")

        w_start = info["window_start"]
        w_end = info["window_end"]
        min_d = info["min_duration"]

        # Duration constraints
        opt.add(dur[person] >= If(meet[person], min_d, 0))
        opt.add(dur[person] >= 0)
        opt.add(dur[person] <= w_end - w_start)

        # Start within window and finish within window
        opt.add(s[person] >= w_start)
        opt.add(s[person] + dur[person] <= w_end)

        # Must be reachable from start location by arrival time
        travel_from_start = travel[start_location][info["location"]]
        opt.add(If(meet[person], s[person] >= arrival_time + travel_from_start, True))

        # Effective end time for makespan objective
        opt.add(end_eff[person] == If(meet[person], s[person] + dur[person], 0))

    # Disjunctive no-overlap with travel times between any two meetings
    people = list(friends.keys())
    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            pi = people[i]
            pj = people[j]
            li = friends[pi]["location"]
            lj = friends[pj]["location"]
            tij = travel[li][lj]
            tji = travel[lj][li]

            # If both meetings occur, enforce separation including travel time
            sep_ij = Or(
                s[pj] >= s[pi] + dur[pi] + tij,
                s[pi] >= s[pj] + dur[pj] + tji
            )
            opt.add(If(And(meet[pi], meet[pj]), sep_ij, True))

    # Objective: maximize number of friends met
    total_met = Sum([If(meet[p], 1, 0) for p in people])
    opt.maximize(total_met)

    # Secondary objective: minimize makespan (latest end among selected meetings)
    makespan = Int("makespan")
    opt.add(makespan >= 0)
    for p in people:
        opt.add(makespan >= end_eff[p])
    opt.minimize(makespan)

    # Solve
    res = opt.check()
    if res != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return

    model = opt.model()

    itinerary = []
    for person in people:
        if is_true(model.evaluate(meet[person], model_completion=True)):
            start_t = model.evaluate(s[person]).as_long()
            end_t = model.evaluate(s[person] + dur[person]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[person]["location"],
                "person": person,
                "start_time": fmt_time(start_t),
                "end_time": fmt_time(end_t),
            })

    # Sort by start time
    def to_minutes(tstr):
        hh, mm = tstr.split(":")
        return int(hh) * 60 + int(mm)

    itinerary.sort(key=lambda x: to_minutes(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()