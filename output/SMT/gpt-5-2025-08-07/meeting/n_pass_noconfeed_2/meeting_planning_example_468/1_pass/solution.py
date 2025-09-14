import json
from z3 import Optimize, Int, Bool, If, Implies, And, Or, Sum

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Locations and travel times (in minutes)
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

    # People, locations, availability windows (in minutes since midnight), minimum meeting duration
    # You arrive at The Castro at 9:00 (540)
    origin_location = "The Castro"
    origin_time = 9 * 60  # 540

    people = {
        "Rebecca": {
            "location": "Bayview",
            "avail_start": 9 * 60,          # 9:00 -> 540
            "avail_end": 12 * 60 + 45,      # 12:45 -> 765
            "min_duration": 90
        },
        "Amanda": {
            "location": "Pacific Heights",
            "avail_start": 18 * 60 + 30,    # 18:30 -> 1110
            "avail_end": 21 * 60 + 45,      # 21:45 -> 1305
            "min_duration": 90
        },
        "James": {
            "location": "Alamo Square",
            "avail_start": 9 * 60 + 45,     # 9:45 -> 585
            "avail_end": 21 * 60 + 15,      # 21:15 -> 1275
            "min_duration": 90
        },
        "Sarah": {
            "location": "Fisherman's Wharf",
            "avail_start": 8 * 60,          # 8:00 -> 480
            "avail_end": 21 * 60 + 30,      # 21:30 -> 1290
            "min_duration": 90
        },
        "Melissa": {
            "location": "Golden Gate Park",
            "avail_start": 9 * 60,          # 9:00 -> 540
            "avail_end": 18 * 60 + 45,      # 18:45 -> 1125
            "min_duration": 90
        },
    }

    names = list(people.keys())
    n = len(names)

    # Z3 model
    opt = Optimize()

    # Variables
    start = {p: Int(f"start_{p}") for p in names}      # start time in minutes
    meet = {p: Bool(f"meet_{p}") for p in names}       # whether we meet the person
    endv = {p: Int(f"end_{p}") for p in names}         # end time in minutes (0 if not meeting)

    # Bounds and constraints per person
    for p in names:
        loc = people[p]["location"]
        a_s = people[p]["avail_start"]
        a_e = people[p]["avail_end"]
        dur = people[p]["min_duration"]

        # Domain bounds for start
        opt.add(start[p] >= 0, start[p] <= 24 * 60)

        # If we meet, start within availability and respect travel from origin
        opt.add(Implies(meet[p], And(
            start[p] >= a_s,
            start[p] + dur <= a_e,
            start[p] >= origin_time + travel[(origin_location, loc)]
        )))
        # If not meeting, set start to 0 (helps anchoring unused vars)
        opt.add(Implies(~meet[p], start[p] == 0))

        # Define end time
        opt.add(endv[p] == If(meet[p], start[p] + dur, 0))

    # Non-overlap and travel-time constraints between any two meetings
    before = {}
    for i in range(n):
        for j in range(i + 1, n):
            p = names[i]
            q = names[j]
            loc_p = people[p]["location"]
            loc_q = people[q]["location"]
            b = Bool(f"before_{p}_{q}")
            before[(p, q)] = b
            dur_p = people[p]["min_duration"]
            dur_q = people[q]["min_duration"]

            # If both meetings happen, enforce one precedes the other including travel time
            opt.add(Implies(And(meet[p], meet[q]),
                            Or(
                                And(b,
                                    start[p] + dur_p + travel[(loc_p, loc_q)] <= start[q]),
                                And(~b,
                                    start[q] + dur_q + travel[(loc_q, loc_p)] <= start[p])
                            )))

    # Define end of day (max end over met meetings) to help select earlier finishing schedule
    end_max = Int("end_max")
    opt.add(end_max >= 0, end_max <= 24 * 60)
    for p in names:
        opt.add(end_max >= endv[p])

    # Objective: maximize number of meetings, then minimize finishing time
    total_meetings = Sum([If(meet[p], 1, 0) for p in names])
    opt.maximize(total_meetings)
    opt.minimize(end_max)

    # Solve
    if opt.check() != 1:
        print(json.dumps({"itinerary": []}))
        return
    m = opt.model()

    # Extract solution
    itinerary = []
    for p in names:
        if m.evaluate(meet[p], model_completion=True):
            s = m.evaluate(start[p], model_completion=True).as_long()
            e = m.evaluate(endv[p], model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": people[p]["location"],
                "person": p,
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e),
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    # SOLUTION:
    main()