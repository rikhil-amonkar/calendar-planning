import json
from z3 import Optimize, Int, Sum, Or, And

def minutes(h, m=0):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    FD = "Financial District"
    CH = "Chinatown"
    AS = "Alamo Square"
    BV = "Bayview"
    FW = "Fisherman's Wharf"

    # Travel times (in minutes), directed as provided
    travel = {
        (FD, CH): 5,  (FD, AS): 17, (FD, BV): 19, (FD, FW): 10,
        (CH, FD): 5,  (CH, AS): 17, (CH, BV): 22, (CH, FW): 8,
        (AS, FD): 17, (AS, CH): 16, (AS, BV): 16, (AS, FW): 19,
        (BV, FD): 19, (BV, CH): 18, (BV, AS): 16, (BV, FW): 25,
        (FW, FD): 11, (FW, CH): 12, (FW, AS): 20, (FW, BV): 26,
    }
    locations = [FD, CH, AS, BV, FW]

    def travel_time(a, b):
        if a == b:
            return 0
        return travel[(a, b)]

    # Participants: availability windows and required minimum meeting durations
    people = [
        {
            "name": "Nancy",
            "location": CH,
            "avail_start": minutes(9, 30),
            "avail_end": minutes(13, 30),
            "min_duration": 90
        },
        {
            "name": "Mary",
            "location": AS,
            "avail_start": minutes(7, 0),
            "avail_end": minutes(21, 0),
            "min_duration": 75
        },
        {
            "name": "Jessica",
            "location": BV,
            "avail_start": minutes(11, 15),
            "avail_end": minutes(13, 45),
            "min_duration": 45
        },
        {
            "name": "Rebecca",
            "location": FW,
            "avail_start": minutes(7, 0),
            "avail_end": minutes(8, 30),
            "min_duration": 45
        },
    ]

    # Day starts arriving at Financial District at 9:00
    day_start_loc = FD
    day_start_time = minutes(9, 0)

    # Big-M value (safely larger than any times in this domain)
    M = minutes(24, 0)

    opt = Optimize()
    opt.set("priority", "lex")

    # Decision variables
    start = {}
    end = {}
    meet = {}
    for p in people:
        n = p["name"]
        start[n] = Int(f"start_{n}")
        end[n] = Int(f"end_{n}")
        meet[n] = Int(f"meet_{n}")  # 0 or 1

        # Domain constraints
        opt.add(meet[n] >= 0, meet[n] <= 1)
        opt.add(start[n] >= 0, end[n] >= 0)

        # Meeting duration exactly minimum when met, zero otherwise
        req = p["min_duration"]
        # end == start + req*meet
        opt.add(end[n] - start[n] == req * meet[n])

        # Availability window constraints (only if meeting occurs)
        a_start = p["avail_start"]
        a_end = p["avail_end"]
        opt.add(start[n] >= a_start - M * (1 - meet[n]))
        opt.add(end[n]   <= a_end   + M * (1 - meet[n]))

        # Earliest possible considering arrival at Financial District and travel to first encounter
        t_travel = travel_time(day_start_loc, p["location"])
        opt.add(start[n] >= day_start_time + t_travel - M * (1 - meet[n]))

    # Non-overlap constraints with travel times between any two meetings if both selected
    for i in range(len(people)):
        for j in range(i + 1, len(people)):
            pi = people[i]
            pj = people[j]
            ni = pi["name"]
            nj = pj["name"]
            li = pi["location"]
            lj = pj["location"]
            tij = travel_time(li, lj)
            tji = travel_time(lj, li)

            # If both meetings occur, enforce order with travel time between them
            opt.add(
                Or(
                    meet[ni] == 0,
                    meet[nj] == 0,
                    end[ni] + tij <= start[nj],
                    end[nj] + tji <= start[ni]
                )
            )

    # Objective 1: maximize number of friends met
    total_met = Sum([meet[p["name"]] for p in people])
    opt.maximize(total_met)

    # Objective 2: minimize the last end time among all meetings (finish earlier)
    last_end = Int("last_end")
    opt.add(last_end >= 0)
    for p in people:
        n = p["name"]
        opt.add(last_end >= end[n])
    opt.minimize(last_end)

    # Solve
    if opt.check() != None:
        model = opt.model()
        selected = []
        for p in people:
            n = p["name"]
            if model[meet[n]].as_long() == 1:
                s = model[start[n]].as_long()
                e = model[end[n]].as_long()
                selected.append({
                    "person": n,
                    "location": p["location"],
                    "start": s,
                    "end": e
                })

        # Sort itinerary by start time
        selected.sort(key=lambda x: x["start"])

        itinerary = []
        for item in selected:
            itinerary.append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": fmt_time(item["start"]),
                "end_time": fmt_time(item["end"])
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()