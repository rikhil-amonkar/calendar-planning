import json
from z3 import Optimize, Int, Bool, And, Or, If, Xor, Sum, Implies, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    Bayview = "Bayview"
    RussianHill = "Russian Hill"
    AlamoSquare = "Alamo Square"
    NorthBeach = "North Beach"
    FinancialDistrict = "Financial District"

    # Travel times (minutes)
    travel = {
        Bayview: {
            RussianHill: 23,
            AlamoSquare: 16,
            NorthBeach: 21,
            FinancialDistrict: 19,
        },
        RussianHill: {
            Bayview: 23,
            AlamoSquare: 15,
            NorthBeach: 5,
            FinancialDistrict: 11,
        },
        AlamoSquare: {
            Bayview: 16,
            RussianHill: 13,
            NorthBeach: 15,
            FinancialDistrict: 17,
        },
        NorthBeach: {
            Bayview: 22,
            RussianHill: 4,
            AlamoSquare: 16,
            FinancialDistrict: 8,
        },
        FinancialDistrict: {
            Bayview: 19,
            RussianHill: 10,
            AlamoSquare: 17,
            NorthBeach: 7,
        },
    }

    def ttime(a, b):
        if a == b:
            return 0
        return travel[a][b]

    # People constraints
    people = {
        "Joseph": {
            "location": RussianHill,
            "avail_start": minutes(8, 30),   # 8:30
            "avail_end": minutes(19, 15),    # 19:15
            "min_duration": 60,
        },
        "Nancy": {
            "location": AlamoSquare,
            "avail_start": minutes(11, 0),   # 11:00
            "avail_end": minutes(16, 0),     # 16:00
            "min_duration": 90,
        },
        "Jason": {
            "location": NorthBeach,
            "avail_start": minutes(16, 45),  # 16:45
            "avail_end": minutes(21, 45),    # 21:45
            "min_duration": 15,
        },
        "Jeffrey": {
            "location": FinancialDistrict,
            "avail_start": minutes(10, 30),  # 10:30
            "avail_end": minutes(15, 45),    # 15:45
            "min_duration": 45,
        },
    }

    # Day start
    day_start = minutes(9, 0)  # 9:00 at Bayview
    day_end_bound = minutes(24, 0)  # Bound horizon

    # Z3 variables
    s = Optimize()
    start_vars = {}
    end_vars = {}
    attend_vars = {}
    before = {}  # before[p][q] means p before q (if both attended)

    # Create variables
    for p in people:
        sp = Int(p.replace(" ", "_") + "_start")
        ep = Int(p.replace(" ", "_") + "_end")
        ap = Bool(p.replace(" ", "_") + "_attend")
        start_vars[p] = sp
        end_vars[p] = ep
        attend_vars[p] = ap
        s.add(sp >= 0, sp <= day_end_bound)
        s.add(ep >= 0, ep <= day_end_bound)
        s.add(ep >= sp)

    # Attendance constraints, availability, durations, start bounds from Bayview
    for p, info in people.items():
        sp = start_vars[p]
        ep = end_vars[p]
        ap = attend_vars[p]
        loc = info["location"]
        avail_s = info["avail_start"]
        avail_e = info["avail_end"]
        min_d = info["min_duration"]

        # If attending, stay within availability and satisfy duration
        s.add(Implies(ap, And(
            sp >= avail_s,
            ep <= avail_e,
            ep - sp >= min_d,
            sp >= day_start + ttime(Bayview, loc)  # can always wait after arriving
        )))
        # If not attending, times are zero (to avoid irrelevant values)
        s.add(Implies(~ap, And(sp == 0, ep == 0)))

    # Pairwise ordering and travel time constraints
    persons = list(people.keys())
    for i in range(len(persons)):
        p = persons[i]
        before[p] = {}
        for j in range(len(persons)):
            if i == j:
                continue
            q = persons[j]
            bvar = Bool(p.replace(" ", "_") + "_before_" + q.replace(" ", "_"))
            before[p][q] = bvar

    for i in range(len(persons)):
        for j in range(i + 1, len(persons)):
            p = persons[i]
            q = persons[j]
            ap = attend_vars[p]
            aq = attend_vars[q]
            bpq = before[p][q]
            bqp = before[q][p]
            sp = start_vars[p]
            ep = end_vars[p]
            sq = start_vars[q]
            eq = end_vars[q]
            lp = people[p]["location"]
            lq = people[q]["location"]

            # If both attended, one must be before the other (no overlap) and enforce travel times
            s.add(Implies(And(ap, aq), Xor(bpq, bqp)))
            s.add(Implies(And(ap, aq, bpq), ep + ttime(lp, lq) <= sq))
            s.add(Implies(And(ap, aq, bqp), eq + ttime(lq, lp) <= sp))

    # Objectives:
    # 1) Maximize number of friends met
    num_met = Sum([If(attend_vars[p], 1, 0) for p in persons])
    s.maximize(num_met)

    # 2) Maximize total meeting time
    total_meet_time = Sum([If(attend_vars[p], end_vars[p] - start_vars[p], 0) for p in persons])
    s.maximize(total_meet_time)

    # 3) Minimize end of day (latest meeting end)
    last_end = Int("last_end")
    s.add(last_end >= 0)
    for p in persons:
        s.add(last_end >= end_vars[p])
    s.minimize(last_end)

    # Solve
    if s.check() != sat:
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    m = s.model()

    # Build itinerary sorted by start time
    entries = []
    for p in persons:
        if m.eval(attend_vars[p], model_completion=True):
            st = m.eval(start_vars[p], model_completion=True).as_long()
            et = m.eval(end_vars[p], model_completion=True).as_long()
            entries.append({
                "action": "meet",
                "location": people[p]["location"],
                "person": p,
                "start_time": fmt_time(st),
                "end_time": fmt_time(et),
            })

    # Sort by start_time (convert back to minutes for sorting)
    def time_to_minutes(tstr):
        h, mnt = tstr.split(":")
        return int(h) * 60 + int(mnt)

    entries.sort(key=lambda e: time_to_minutes(e["start_time"]))

    output = {"itinerary": entries}
    print(json.dumps(output))

if __name__ == "__main__":
    main()