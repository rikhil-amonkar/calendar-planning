import json
from z3 import Optimize, Int, And, Or, If, Implies, Sum, sat

def to_minutes(h, m):
    return h * 60 + m

def m2str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    RH = "Russian Hill"
    NH = "Nob Hill"
    MD = "Mission District"
    EMB = "Embarcadero"

    # Travel times (minutes), directional
    travel = {
        (RH, NH): 5,   (RH, MD): 16,  (RH, EMB): 8,
        (NH, RH): 5,   (NH, MD): 13,  (NH, EMB): 9,
        (MD, RH): 15,  (MD, NH): 12,  (MD, EMB): 19,
        (EMB, RH): 8,  (EMB, NH): 10, (EMB, MD): 20
    }

    # Add zero-time self travel to prevent KeyError on same-location transitions
    locations = [RH, NH, MD, EMB]
    for loc in locations:
        travel[(loc, loc)] = 0

    # People mapping: id -> info
    # ids: 1=Timothy, 2=Patricia, 3=Ashley
    people = {
        1: {"name": "Timothy", "location": EMB, "avail_start": to_minutes(9,45),  "avail_end": to_minutes(17,45), "min_meet": 120},
        2: {"name": "Patricia","location": NH,  "avail_start": to_minutes(18,30), "avail_end": to_minutes(21,45), "min_meet": 90},
        3: {"name": "Ashley",  "location": MD,  "avail_start": to_minutes(20,30), "avail_end": to_minutes(21,15), "min_meet": 45}
    }

    # Start info
    day_start_loc = RH
    day_start_time = to_minutes(9, 0)

    # Number of meeting slots (max one per person)
    K = 3

    opt = Optimize()

    meet = [Int(f"meet_{i}") for i in range(K)]         # 0=unused, 1..3 person id
    start = [Int(f"start_{i}") for i in range(K)]       # minutes from 00:00
    end = [Int(f"end_{i}") for i in range(K)]           # minutes from 00:00

    # Domains and basic constraints
    for i in range(K):
        # meet_i domain
        opt.add(And(meet[i] >= 0, meet[i] <= 3))
        # time bounds
        opt.add(And(start[i] >= 0, start[i] <= 24*60))
        opt.add(And(end[i] >= 0, end[i] <= 24*60))
        # If unused, zero out times to avoid interfering
        opt.add(Implies(meet[i] == 0, And(start[i] == 0, end[i] == 0)))
        # If used, end after start
        opt.add(Implies(meet[i] > 0, end[i] > start[i]))

        # Availability and minimum duration per person
        for p in people:
            info = people[p]
            opt.add(Implies(
                meet[i] == p,
                And(
                    start[i] >= info["avail_start"],
                    end[i]   <= info["avail_end"],
                    end[i] - start[i] >= info["min_meet"]
                )
            ))

    # Consecutive usage: once an unused slot occurs, all following must be unused
    for i in range(K-1):
        opt.add(Implies(meet[i] == 0, meet[i+1] == 0))

    # No duplicate people across used slots
    for i in range(K):
        for j in range(i+1, K):
            opt.add(Or(meet[i] == 0, meet[j] == 0, meet[i] != meet[j]))

    # Travel constraints
    # From start location to first used slot
    for p in people:
        loc_p = people[p]["location"]
        t = travel.get((day_start_loc, loc_p), 0)
        opt.add(Implies(meet[0] == p, start[0] >= day_start_time + t))

    # Between consecutive used slots
    for i in range(1, K):
        for p_prev in people:
            loc_prev = people[p_prev]["location"]
            for p_curr in people:
                loc_curr = people[p_curr]["location"]
                t = travel.get((loc_prev, loc_curr), 0)
                opt.add(Implies(And(meet[i-1] == p_prev, meet[i] == p_curr),
                                start[i] >= end[i-1] + t))

    # Objective 1: maximize number of friends met
    meet_count = Sum([If(meet[i] == 0, 0, 1) for i in range(K)])
    opt.maximize(meet_count)

    # Objective 2: maximize total meeting minutes
    total_meeting_minutes = Sum([If(meet[i] == 0, 0, end[i] - start[i]) for i in range(K)])
    opt.maximize(total_meeting_minutes)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Build itinerary in order
    itinerary = []
    for i in range(K):
        mi = model.evaluate(meet[i]).as_long()
        if mi == 0:
            continue
        info = people[mi]
        s = model.evaluate(start[i]).as_long()
        e = model.evaluate(end[i]).as_long()
        itinerary.append({
            "action": "meet",
            "location": info["location"],
            "person": info["name"],
            "start_time": m2str(s),
            "end_time": m2str(e)
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()