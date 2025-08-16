# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def solve():
    # Locations
    GGP = "Golden Gate Park"
    AS = "Alamo Square"
    PR = "Presidio"
    RH = "Russian Hill"

    # Travel times (minutes), directional
    travel = {
        (GGP, AS): 10, (AS, GGP): 9,
        (GGP, PR): 11, (PR, GGP): 12,
        (GGP, RH): 19, (RH, GGP): 21,
        (AS, PR): 18, (PR, AS): 18,
        (AS, RH): 13, (RH, AS): 15,
        (PR, RH): 14, (RH, PR): 14,
    }
    # Add zero for same-location moves
    locations = {GGP, AS, PR, RH}
    for loc in locations:
        travel[(loc, loc)] = 0

    start_at_time = 9 * 60  # 09:00 at Golden Gate Park

    # People data
    people = [
        {
            "name": "Timothy",
            "loc": AS,
            "avail_start": 12 * 60,           # 12:00
            "avail_end": 16 * 60 + 15,        # 16:15
            "min_dur": 105
        },
        {
            "name": "Mark",
            "loc": PR,
            "avail_start": 18 * 60 + 45,      # 18:45
            "avail_end": 21 * 60,             # 21:00
            "min_dur": 60
        },
        {
            "name": "Joseph",
            "loc": RH,
            "avail_start": 16 * 60 + 45,      # 16:45
            "avail_end": 21 * 60 + 30,        # 21:30
            "min_dur": 60
        },
    ]

    n = len(people)

    # Z3 variables
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    meet = [Bool(f"meet_{i}") for i in range(n)]
    first = [Bool(f"first_{i}") for i in range(n)]
    order = [[Bool(f"order_{i}_{j}") if i != j else BoolVal(False) for j in range(n)] for i in range(n)]

    opt = Optimize()

    # Domains and basic constraints
    for i in range(n):
        # Domain for times
        opt.add(start[i] >= 0, start[i] <= 24 * 60)
        opt.add(end[i] >= 0, end[i] <= 24 * 60)
        opt.add(end[i] >= start[i])

        # Meeting feasibility when chosen
        ps = people[i]
        opt.add(Implies(meet[i], And(
            start[i] >= ps["avail_start"],
            end[i] <= ps["avail_end"],
            end[i] - start[i] >= ps["min_dur"]
        )))

        # 'first' implies meeting, and reachable from start location/time
        opt.add(Implies(first[i], meet[i]))
        opt.add(Implies(first[i], start[i] >= start_at_time + travel[(GGP, ps["loc"])]]))

    # Antisymmetry for order variables: order[i][j] == Not(order[j][i]) for i != j
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            opt.add(order[i][j] == Not(order[j][i]))

    # Sequencing constraints with travel times
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            li = people[i]["loc"]
            lj = people[j]["loc"]
            tij = travel[(li, lj)]
            tji = travel[(lj, li)]
            # If we meet both and i before j, ensure travel and timing feasibility
            opt.add(Implies(And(meet[i], meet[j], order[i][j]),
                            end[i] + tij <= start[j]))
            # If j before i
            opt.add(Implies(And(meet[i], meet[j], order[j][i]),
                            end[j] + tji <= start[i]))

    # Every met meeting must either be first or have a predecessor
    for i in range(n):
        predecessors = []
        for j in range(n):
            if i == j:
                continue
            predecessors.append(And(meet[j], order[j][i]))
        if predecessors:
            opt.add(Implies(meet[i], Or(first[i], Or(predecessors))))
        else:
            # Only one person case: must be first if met
            opt.add(Implies(meet[i], first[i]))

    # Exactly one 'first' if we meet at least one person
    total_met = Int("total_met")
    sum_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.add(total_met == sum_meet)
    sum_first = Sum([If(first[i], 1, 0) for i in range(n)])
    opt.add(Or(total_met == 0, sum_first == 1))

    # Objective 1: maximize number of friends met
    opt.maximize(total_met)

    # Objective 2: among max, finish as early as possible
    last_end = Int("last_end")
    opt.add(last_end >= 0, last_end <= 24 * 60)
    for i in range(n):
        opt.add(Implies(meet[i], last_end >= end[i]))
    opt.minimize(last_end)

    # Solve
    if opt.check() != sat:
        # No feasible schedule
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    # Extract chosen meetings and times
    meetings = []
    for i in range(n):
        if is_true(m.evaluate(meet[i])):
            s = m.evaluate(start[i]).as_long()
            e = m.evaluate(end[i]).as_long()
            meetings.append({
                "action": "meet",
                "person": people[i]["name"],
                "start": s,
                "end": e
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    # Format times
    itinerary = []
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "person": mt["person"],
            "start_time": to_hhmm(mt["start"]),
            "end_time": to_hhmm(mt["end"])
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    solve()