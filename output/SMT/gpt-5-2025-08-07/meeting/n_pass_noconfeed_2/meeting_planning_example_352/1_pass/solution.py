import json
from z3 import Optimize, Int, Bool, And, Or, Implies, If, Sum

def min_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def solve():
    # Locations
    US = "Union Square"
    NH = "Nob Hill"
    HA = "Haight-Ashbury"
    CT = "Chinatown"
    MD = "Marina District"

    # Travel times in minutes (directed)
    travel = {
        (US, NH): 9,
        (US, HA): 18,
        (US, CT): 7,
        (US, MD): 18,

        (NH, US): 7,
        (NH, HA): 13,
        (NH, CT): 6,
        (NH, MD): 11,

        (HA, US): 17,
        (HA, NH): 15,
        (HA, CT): 19,
        (HA, MD): 17,

        (CT, US): 7,
        (CT, NH): 8,
        (CT, HA): 19,
        (CT, MD): 12,

        (MD, US): 16,
        (MD, NH): 12,
        (MD, HA): 16,
        (MD, CT): 16,
    }

    # People data: location, availability start, availability end, minimum meeting duration
    # Times in minutes since midnight
    people = {
        "Karen":  {"location": NH, "avail_start": 21*60+15, "avail_end": 21*60+45, "min_dur": 30},
        "Joseph": {"location": HA, "avail_start": 12*60+30, "avail_end": 19*60+45, "min_dur": 90},
        "Sandra": {"location": CT, "avail_start": 7*60+15,  "avail_end": 19*60+15, "min_dur": 75},
        "Nancy":  {"location": MD, "avail_start": 11*60,    "avail_end": 20*60+15, "min_dur": 105},
    }

    arrival_loc = US
    arrival_time = 9*60  # 9:00

    # Z3 variables
    starts = {p: Int(f"start_{p}") for p in people}
    ends   = {p: Int(f"end_{p}")   for p in people}
    durs   = {p: Int(f"dur_{p}")   for p in people}
    meets  = {p: Bool(f"meet_{p}") for p in people}

    opt = Optimize()

    # Domain constraints
    for p, info in people.items():
        s, e, d, m = starts[p], ends[p], durs[p], meets[p]
        avail_s, avail_e, min_d = info["avail_start"], info["avail_end"], info["min_dur"]
        loc = info["location"]

        # General bounds
        opt.add(s >= 0, s <= 24*60)
        opt.add(e >= 0, e <= 24*60)
        opt.add(d >= 0)

        # If meeting occurs, must fit availability and minimum duration
        opt.add(Implies(m, And(
            s >= avail_s,
            e <= avail_e,
            d >= min_d,
            e == s + d
        )))

        # If not meeting, duration is 0 and start/end can be arbitrary within bounds; set e == s for neatness
        opt.add(Implies(~m, And(
            d == 0,
            e == s
        )))

        # Able to get from arrival location to this meeting's start
        # This ensures the earliest meeting respects travel from the starting point.
        if (arrival_loc, loc) in travel:
            opt.add(Implies(m, s >= arrival_time + travel[(arrival_loc, loc)]))
        else:
            # If no direct travel entry, disallow meeting (shouldn't happen given the data)
            opt.add(~m)

    # Pairwise non-overlap with travel time between meetings when both are scheduled
    persons = list(people.keys())
    for i in range(len(persons)):
        for j in range(i+1, len(persons)):
            pi, pj = persons[i], persons[j]
            li, lj = people[pi]["location"], people[pj]["location"]
            ti_to_j = travel[(li, lj)]
            tj_to_i = travel[(lj, li)]
            si, ei = starts[pi], ends[pi]
            sj, ej = starts[pj], ends[pj]
            mi, mj = meets[pi], meets[pj]

            # If both meetings occur, enforce an order with travel time
            opt.add(Implies(And(mi, mj),
                            Or(ei + ti_to_j <= sj,
                               ej + tj_to_i <= si)))

    # Objectives:
    num_met = Sum([If(meets[p], 1, 0) for p in people])
    total_meeting_time = Sum([durs[p] for p in people])  # 0 if not meeting
    opt.maximize(num_met)
    opt.maximize(total_meeting_time)

    # Solve
    if opt.check() != None:
        model = opt.model()
        itinerary = []
        # Collect scheduled meetings
        scheduled = []
        for p in people:
            if model.eval(meets[p], model_completion=True):
                st = model.eval(starts[p]).as_long()
                en = model.eval(ends[p]).as_long()
                # Only include if meeting is indeed scheduled with positive duration
                if en > st:
                    scheduled.append((st, en, p, people[p]["location"]))

        # Sort by start time
        scheduled.sort(key=lambda x: x[0])

        for st, en, p, loc in scheduled:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": p,
                "start_time": min_to_str(st),
                "end_time": min_to_str(en)
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        print(json.dumps({"itinerary": []}, ensure_ascii=False))

if __name__ == "__main__":
    solve()