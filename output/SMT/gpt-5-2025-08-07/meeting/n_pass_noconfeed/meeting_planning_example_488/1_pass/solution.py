import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat

def to_minutes(tstr):
    # tstr format 'H:MM' or 'HH:MM'
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def to_timestr(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Locations
    PH = "Pacific Heights"
    locations = [
        "Pacific Heights",
        "Nob Hill",
        "Russian Hill",
        "The Castro",
        "Sunset District",
        "Haight-Ashbury"
    ]

    # Travel times (minutes)
    travel = {
        "Pacific Heights": {
            "Nob Hill": 8,
            "Russian Hill": 7,
            "The Castro": 16,
            "Sunset District": 21,
            "Haight-Ashbury": 11
        },
        "Nob Hill": {
            "Pacific Heights": 8,
            "Russian Hill": 5,
            "The Castro": 17,
            "Sunset District": 25,
            "Haight-Ashbury": 13
        },
        "Russian Hill": {
            "Pacific Heights": 7,
            "Nob Hill": 5,
            "The Castro": 21,
            "Sunset District": 23,
            "Haight-Ashbury": 17
        },
        "The Castro": {
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Russian Hill": 18,
            "Sunset District": 17,
            "Haight-Ashbury": 6
        },
        "Sunset District": {
            "Pacific Heights": 21,
            "Nob Hill": 27,
            "Russian Hill": 24,
            "The Castro": 17,
            "Haight-Ashbury": 15
        },
        "Haight-Ashbury": {
            "Pacific Heights": 12,
            "Nob Hill": 15,
            "Russian Hill": 17,
            "The Castro": 6,
            "Sunset District": 15
        }
    }

    # People data: location, availability window, and minimum meeting duration
    people = {
        "Ronald":   {"location": "Nob Hill",         "avail": ("10:00", "17:00"), "min_duration": 105},
        "Sarah":    {"location": "Russian Hill",     "avail": ("7:15",  "9:30"),  "min_duration": 45},
        "Helen":    {"location": "The Castro",       "avail": ("13:30", "17:00"), "min_duration": 120},
        "Joshua":   {"location": "Sunset District",  "avail": ("14:15", "19:30"), "min_duration": 90},
        "Margaret": {"location": "Haight-Ashbury",   "avail": ("10:15", "22:00"), "min_duration": 60}
    }

    # Arrival info
    arrival_location = "Pacific Heights"
    arrival_time = to_minutes("9:00")
    day_end = to_minutes("23:59")

    # Create solver
    opt = Optimize()

    # Variables per person
    start_vars = {}
    meet_vars = {}
    durations = {}
    avail_starts = {}
    avail_ends = {}
    loc_of = {}

    for name, info in people.items():
        start_vars[name] = Int(f"start_{name}")
        meet_vars[name] = Bool(f"meet_{name}")
        durations[name] = info["min_duration"]
        avail_starts[name] = to_minutes(info["avail"][0])
        avail_ends[name] = to_minutes(info["avail"][1])
        loc_of[name] = info["location"]

        # Domain and basic constraints
        opt.add(start_vars[name] >= 0, start_vars[name] <= day_end)
        # If meeting, must fit within availability and day
        opt.add(Implies(meet_vars[name],
                        And(start_vars[name] >= avail_starts[name],
                            start_vars[name] + durations[name] <= avail_ends[name],
                            start_vars[name] + durations[name] <= day_end)))
        # Feasible from arrival location at 9:00
        t0 = travel[arrival_location][loc_of[name]]
        opt.add(Implies(meet_vars[name], start_vars[name] >= arrival_time + t0))

    # Pairwise non-overlap with travel times
    names = list(people.keys())
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            ni, nj = names[i], names[j]
            li, lj = loc_of[ni], loc_of[nj]
            dij = travel[li][lj]
            dji = travel[lj][li]
            # If both meetings happen, enforce one precedes the other with travel
            opt.add(Implies(And(meet_vars[ni], meet_vars[nj]),
                            Or(start_vars[ni] + durations[ni] + dij <= start_vars[nj],
                               start_vars[nj] + durations[nj] + dji <= start_vars[ni])))

    # Objective: maximize the number of friends met
    meet_count = Sum([If(meet_vars[n], 1, 0) for n in names])
    opt.maximize(meet_count)

    # Solve
    result = opt.check()
    itinerary = []

    if result == sat:
        model = opt.model()
        selected = []
        for n in names:
            if model.eval(meet_vars[n], model_completion=True):
                start = model.eval(start_vars[n]).as_long()
                end = start + durations[n]
                selected.append((start, {
                    "action": "meet",
                    "location": loc_of[n],
                    "person": n,
                    "start_time": to_timestr(start),
                    "end_time": to_timestr(end)
                })))
        # Sort by start time
        selected.sort(key=lambda x: x[0])
        itinerary = [entry for _, entry in selected]
    else:
        itinerary = []

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()