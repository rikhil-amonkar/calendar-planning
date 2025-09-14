import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def build_travel_times():
    # Directed travel times in minutes
    return {
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Bayview"): 22,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Fisherman's Wharf"): 25,
    }

def main():
    # Constants
    start_location = "Nob Hill"
    day_start = 9 * 60  # 9:00 AM in minutes since midnight

    # People and constraints
    people = [
        {
            "name": "Helen",
            "location": "North Beach",
            "avail_start": 7 * 60,        # 7:00
            "avail_end": 16 * 60 + 45,    # 16:45
            "min_meet": 120
        },
        {
            "name": "Kimberly",
            "location": "Fisherman's Wharf",
            "avail_start": 16 * 60 + 30,  # 16:30
            "avail_end": 21 * 60,         # 21:00
            "min_meet": 45
        },
        {
            "name": "Patricia",
            "location": "Bayview",
            "avail_start": 18 * 60,       # 18:00
            "avail_end": 21 * 60 + 15,    # 21:15
            "min_meet": 120
        }
    ]

    # Index mapping to ensure distinctness with ord=0 allowed
    idx_map = {p["name"]: i+1 for i, p in enumerate(people)}  # 1..3

    travel = build_travel_times()

    def ttime(a, b):
        return travel[(a, b)]

    # Z3 variables
    s_vars = {p["name"]: Int(f"s_{p['name']}") for p in people}
    e_vars = {p["name"]: Int(f"e_{p['name']}") for p in people}
    ord_vars = {p["name"]: Int(f"ord_{p['name']}") for p in people}

    solver = Optimize()

    # Bounds and basic constraints
    for p in people:
        name = p["name"]
        s = s_vars[name]
        e = e_vars[name]
        ordv = ord_vars[name]

        # Time bounds
        solver.add(s >= 0, s <= 24*60)
        solver.add(e >= 0, e <= 24*60)
        solver.add(e >= s)

        # Order bounds: 0 means not meeting; 1..3 are sequence positions
        solver.add(ordv >= 0, ordv <= 3)

        # If meeting (ord>0), enforce availability and minimum duration
        solver.add(Implies(ordv > 0, s >= p["avail_start"]))
        solver.add(Implies(ordv > 0, e <= p["avail_end"]))
        solver.add(Implies(ordv > 0, e - s >= p["min_meet"]))

        # If not meeting, collapse interval to a single point (e.g., 0)
        solver.add(Implies(ordv == 0, s == 0))
        solver.add(Implies(ordv == 0, e == 0))

    # Distinctness of orders for meetings; allow multiple zeros by mapping zeros to unique negatives
    mapped_orders = []
    for p in people:
        name = p["name"]
        ordv = ord_vars[name]
        mapped_orders.append(If(ordv == 0, IntVal(-idx_map[name]), ordv))
    solver.add(Distinct(mapped_orders))

    # Number of meetings to maximize
    n_meet = Sum([If(ord_vars[p["name"]] > 0, IntVal(1), IntVal(0)) for p in people])
    solver.maximize(n_meet)

    # Ensure orders are contiguous 1..n_meet (no gaps)
    for p in people:
        name = p["name"]
        ordv = ord_vars[name]
        solver.add(Implies(ordv > 0, ordv <= n_meet))

    # Travel chain constraints: link each meeting to its predecessor (or start)
    for p in people:
        name = p["name"]
        loc = p["location"]
        s = s_vars[name]
        ordv = ord_vars[name]

        # If this is the first meeting, leave from start location at day_start
        solver.add(Implies(ordv == 1, s >= day_start + ttime(start_location, loc)))

        # If this is not the first, it must start after the previous in the sequence plus travel time
        for q in people:
            if q["name"] == name:
                continue
            prev_ord = ord_vars[q["name"]]
            e_prev = e_vars[q["name"]]
            solver.add(Implies(And(ordv > 1, prev_ord == ordv - 1),
                               s >= e_prev + ttime(q["location"], loc)))

    # Solve
    if solver.check() != sat:
        # No feasible schedule
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = solver.model()

    # Build itinerary sorted by order
    meetings = []
    for p in people:
        name = p["name"]
        loc = p["location"]
        ord_val = model.eval(ord_vars[name]).as_long()
        if ord_val > 0:
            s_val = model.eval(s_vars[name]).as_long()
            e_val = model.eval(e_vars[name]).as_long()
            meetings.append((ord_val, {
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_str(s_val),
                "end_time": minutes_to_str(e_val)
            }))

    meetings.sort(key=lambda x: x[0])
    itinerary = [m[1] for m in meetings]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()