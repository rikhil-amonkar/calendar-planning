import json
from z3 import *

def time_to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Define locations and travel times (in minutes)
    locations = [
        "The Castro",
        "Bayview",
        "Pacific Heights",
        "Alamo Square",
        "Fisherman's Wharf",
        "Golden Gate Park",
    ]

    travel = {
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Golden Gate Park"): 11,

        ("Bayview", "The Castro"): 20,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Golden Gate Park"): 22,

        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,

        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Golden Gate Park"): 9,

        ("Fisherman's Wharf", "The Castro"): 26,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,

        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
    }

    # People and their availability (start, end) in minutes from midnight
    # You arrive at The Castro at 9:00 (540)
    # Minimum meeting duration for everyone is 90 minutes
    people = [
        {
            "name": "Rebecca",
            "location": "Bayview",
            "avail_start": time_to_minutes(9, 0),     # 9:00
            "avail_end": time_to_minutes(12, 45),     # 12:45
        },
        {
            "name": "Amanda",
            "location": "Pacific Heights",
            "avail_start": time_to_minutes(18, 30),   # 18:30
            "avail_end": time_to_minutes(21, 45),     # 21:45
        },
        {
            "name": "James",
            "location": "Alamo Square",
            "avail_start": time_to_minutes(9, 45),    # 9:45
            "avail_end": time_to_minutes(21, 15),     # 21:15
        },
        {
            "name": "Sarah",
            "location": "Fisherman's Wharf",
            "avail_start": time_to_minutes(8, 0),     # 8:00
            "avail_end": time_to_minutes(21, 30),     # 21:30
        },
        {
            "name": "Melissa",
            "location": "Golden Gate Park",
            "avail_start": time_to_minutes(9, 0),     # 9:00
            "avail_end": time_to_minutes(18, 45),     # 18:45
        },
    ]

    start_location = "The Castro"
    arrival_time = time_to_minutes(9, 0)   # 9:00
    day_end = time_to_minutes(22, 0)       # 22:00 cutoff for the day
    min_meeting = 90

    opt = Optimize()
    opt.set(priority='lex')

    # Variables
    meet = {}
    start = {}
    dur = {}
    end = {}

    for p in people:
        name = p["name"]
        meet[name] = Bool(f"meet_{name}")
        start[name] = Int(f"start_{name}")
        dur[name] = Int(f"dur_{name}")
        end[name] = Int(f"end_{name}")

        # Duration exactly 90 if meeting, else 0
        opt.add(dur[name] == If(meet[name], min_meeting, 0))

        # End time definition
        opt.add(end[name] == start[name] + dur[name])

        # If meeting, respect availability window
        opt.add(Implies(meet[name], And(
            start[name] >= p["avail_start"],
            end[name] <= p["avail_end"]
        )))

        # Bound variables within the day for sanity
        opt.add(start[name] >= 0, start[name] <= day_end)
        opt.add(end[name] >= 0, end[name] <= day_end)

        # If meeting, must be able to travel from arrival location at 9:00
        base_travel = travel[(start_location, p["location"])]
        opt.add(Implies(meet[name], start[name] >= arrival_time + base_travel))

    # Disjunctive ordering constraints with travel times between any two meetings
    order = {}
    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            a = people[i]
            b = people[j]
            ai = a["name"]
            bj = b["name"]
            order[(ai, bj)] = Bool(f"order_{ai}_before_{bj}")
            t_ab = travel[(a["location"], b["location"])]
            t_ba = travel[(b["location"], a["location"])]

            # If both are met, either a before b with travel, or b before a with travel
            opt.add(Implies(And(meet[ai], meet[bj]),
                            Or(
                                And(order[(ai, bj)],
                                    start[bj] >= end[ai] + t_ab),
                                And(Not(order[(ai, bj)]),
                                    start[ai] >= end[bj] + t_ba)
                            )))

    # Objective 1: maximize number of meetings
    total_meetings = Sum([If(meet[p["name"]], 1, 0) for p in people])
    opt.maximize(total_meetings)

    # Objective 2: minimize the overall latest end time (makespan)
    makespan = Int("makespan")
    opt.add(makespan >= 0, makespan <= day_end)
    for p in people:
        name = p["name"]
        opt.add(Implies(meet[name], makespan >= end[name]))
    opt.minimize(makespan)

    # Objective 3: minimize sum of start times (to prefer earlier feasible schedule)
    opt.minimize(Sum([If(meet[p["name"]], start[p["name"]], 0) for p in people]))

    if opt.check() != sat:
        # No feasible schedule
        print(json.dumps({"itinerary": []}, indent=2))
        return

    model = opt.model()

    itinerary = []
    for p in people:
        name = p["name"]
        if is_true(model[meet[name]]):
            s = model[start[name]].as_long()
            e = model[end[name]].as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e),
            })

    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()