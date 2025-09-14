from z3 import *
import json

def main():
    # Convert times to minutes from midnight
    # For example, 9:00 AM is 9*60 = 540, etc.
    friends = [
        {"name": "Karen", "location": "Russian Hill", "avail_start": 20*60 + 45, "avail_end": 21*60 + 45, "min_duration": 60},
        {"name": "Jessica", "location": "The Castro", "avail_start": 15*60 + 45, "avail_end": 19*60 + 30, "min_duration": 60},
        {"name": "Matthew", "location": "Richmond District", "avail_start": 7*60 + 30, "avail_end": 15*60 + 15, "min_duration": 15},
        {"name": "Michelle", "location": "Marina District", "avail_start": 10*60 + 30, "avail_end": 18*60 + 45, "min_duration": 75},
        {"name": "Carol", "location": "North Beach", "avail_start": 12*60, "avail_end": 17*60, "min_duration": 90},
        {"name": "Stephanie", "location": "Union Square", "avail_start": 10*60 + 45, "avail_end": 14*60 + 15, "min_duration": 30},
        {"name": "Linda", "location": "Golden Gate Park", "avail_start": 10*60 + 45, "avail_end": 22*60, "min_duration": 90},
    ]

    # Travel times between districts in minutes
    travel_times = {
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 29,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Golden Gate Park"): 11,

        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11,
        ("Russian Hill", "Golden Gate Park"): 21,

        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Golden Gate Park"): 11,

        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Golden Gate Park"): 9,

        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Golden Gate Park"): 18,

        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Golden Gate Park"): 22,

        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Golden Gate Park"): 22,

        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Union Square"): 22,
    }
    
    s = Optimize()

    n = len(friends)
    
    # Decision variables for each friend meeting:
    # meet[i]: whether we schedule a meeting with friend[i]
    # start[i], end[i]: meeting start and end times (in minutes from midnight)
    # order[i]: order in the itinerary (0 if not scheduled, otherwise a positive integer)
    meets = [Bool(f"meet_{i}") for i in range(n)]
    starts = [Int(f"start_{i}") for i in range(n)]
    ends = [Int(f"end_{i}") for i in range(n)]
    orders = [Int(f"order_{i}") for i in range(n)]
    
    # Add constraints for each meeting if scheduled
    for i, friend in enumerate(friends):
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_dur = friend["min_duration"]
        # Meeting time must lie within friend's available window.
        s.add(Implies(meets[i], starts[i] >= avail_start))
        s.add(Implies(meets[i], ends[i] <= avail_end))
        s.add(Implies(meets[i], ends[i] - starts[i] >= min_dur))
        # If not meeting, force order 0.
        s.add(Implies(Not(meets[i]), orders[i] == 0))
        # If meeting is scheduled, order is between 1 and n.
        s.add(Implies(meets[i], And(orders[i] >= 1, orders[i] <= n)))
    
    # Enforce that no two scheduled meetings have the same order.
    for i in range(n):
        for j in range(i+1, n):
            s.add(Implies(And(meets[i], meets[j]), orders[i] != orders[j]))
    
    # Enforce contiguity: every meeting (except the first) must have a predecessor.
    for i in range(n):
        s.add(Implies(And(meets[i], orders[i] > 1),
                      Or([And(meets[j], orders[j] == orders[i] - 1) for j in range(n) if j != i])))
    
    # For the first meeting in the itinerary, account for travel from Sunset District (arrival at 9:00AM => 540)
    for i in range(n):
        tt = travel_times.get(("Sunset District", friends[i]["location"]))
        if tt is not None:
            s.add(Implies(And(meets[i], orders[i] == 1), 540 + tt <= starts[i]))
    
    # For consecutive meetings, ensure that travel time between meeting locations is respected.
    for i in range(n):
        for j in range(n):
            if i != j:
                tt = travel_times.get((friends[i]["location"], friends[j]["location"]))
                if tt is not None:
                    s.add(Implies(And(meets[i], meets[j], orders[j] == orders[i] + 1),
                                  ends[i] + tt <= starts[j]))
    
    # Objective: maximize the number of meetings scheduled
    total_meetings = Sum([If(m, 1, 0) for m in meets])
    s.maximize(total_meetings)
    
    if s.check() == sat:
        m = s.model()
        scheduled = []
        for i in range(n):
            if m.evaluate(meets[i]):
                order_val = m.evaluate(orders[i]).as_long()
                start_val = m.evaluate(starts[i]).as_long()
                end_val = m.evaluate(ends[i]).as_long()
                scheduled.append((order_val, friends[i]["location"], friends[i]["name"], start_val, end_val))
        # Sort scheduled meetings by their itinerary order
        scheduled.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, location, name, start_val, end_val in scheduled:
            start_hour = start_val // 60
            start_min = start_val % 60
            end_hour = end_val // 60
            end_min = end_val % 60
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": f"{start_hour}:{start_min:02d}",
                "end_time": f"{end_hour}:{end_min:02d}"
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()