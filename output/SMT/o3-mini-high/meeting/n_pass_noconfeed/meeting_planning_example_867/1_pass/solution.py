from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Define friend meeting constraints: name, location, available start/end (in minutes after midnight), and minimum meeting duration.
    friends = [
        {"name": "Elizabeth", "location": "Mission District", "avail_start": 630, "avail_end": 1200, "min_duration": 90},
        {"name": "David", "location": "Union Square", "avail_start": 915, "avail_end": 1140, "min_duration": 45},
        {"name": "Sandra", "location": "Pacific Heights", "avail_start": 420, "avail_end": 1200, "min_duration": 120},
        {"name": "Thomas", "location": "Bayview", "avail_start": 1170, "avail_end": 1230, "min_duration": 30},
        {"name": "Robert", "location": "Fisherman's Wharf", "avail_start": 600, "avail_end": 900, "min_duration": 15},
        {"name": "Kenneth", "location": "Marina District", "avail_start": 645, "avail_end": 780, "min_duration": 45},
        {"name": "Melissa", "location": "Richmond District", "avail_start": 1095, "avail_end": 1200, "min_duration": 15},
        {"name": "Kimberly", "location": "Sunset District", "avail_start": 615, "avail_end": 1095, "min_duration": 105},
        {"name": "Amanda", "location": "Golden Gate Park", "avail_start": 465, "avail_end": 1125, "min_duration": 15},
    ]
    n = len(friends)
    
    # Define travel times (in minutes) between locations (non-symmetric).
    travel = {
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,

        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Golden Gate Park"): 17,

        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Golden Gate Park"): 22,

        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Golden Gate Park"): 15,

        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Golden Gate Park"): 22,

        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,

        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Golden Gate Park"): 18,

        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Golden Gate Park"): 9,

        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Golden Gate Park"): 11,

        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
    }
    
    # Create an Optimize object.
    opt = Optimize()

    # Decision variables: each friend gets a start time, end time, and an order in the itinerary.
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]  # 0 means not scheduled, otherwise a positive integer
  
    # Domain constraints for time (0 to 1440 minutes) and order (0 or 1..n).
    for i in range(n):
        opt.add(start_vars[i] >= 0, start_vars[i] <= 1440)
        opt.add(end_vars[i] >= 0, end_vars[i] <= 1440)
        opt.add(order_vars[i] >= 0, order_vars[i] <= n)
    
    # For each friend, if scheduled (order > 0), then enforce the meeting's availability and minimum duration.
    for i, friend in enumerate(friends):
        a_start = friend["avail_start"]
        a_end = friend["avail_end"]
        min_dur = friend["min_duration"]
        opt.add(Implies(order_vars[i] > 0, start_vars[i] >= a_start))
        opt.add(Implies(order_vars[i] > 0, end_vars[i] <= a_end))
        opt.add(Implies(order_vars[i] > 0, end_vars[i] >= start_vars[i] + min_dur))
    
    # Ensure that scheduled meetings get unique order numbers.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(order_vars[i] > 0, order_vars[j] > 0),
                            order_vars[i] != order_vars[j]))
    
    # Enforce that scheduled meeting orders are contiguous:
    # If any meeting is assigned order m+1, then some meeting must have order m.
    for m in range(1, n):
        opt.add(Implies(Or([order_vars[i] == m+1 for i in range(n)]),
                        Or([order_vars[j] == m for j in range(n)])))
    
    # For the first meeting in the itinerary (order == 1), ensure arrival from Haight-Ashbury at 9:00 AM (540 minutes)
    # plus the travel time from Haight-Ashbury to that meeting's location.
    for i, friend in enumerate(friends):
        tt = travel[("Haight-Ashbury", friend["location"])]
        opt.add(Implies(order_vars[i] == 1, start_vars[i] >= 540 + tt))
    
    # For consecutive meetings, ensure that the start time of the meeting with order k+1 is at least the finish time
    # of the meeting with order k plus travel time between their locations.
    for i in range(n):
        for j in range(n):
            if i != j:
                tt = travel[(friends[i]["location"], friends[j]["location"])]
                opt.add(Implies(And(order_vars[i] > 0, order_vars[j] > 0, order_vars[j] == order_vars[i] + 1),
                                start_vars[j] >= end_vars[i] + tt))
    
    # Objective: maximize the total number of meetings scheduled.
    total_meetings = Sum([If(order_vars[i] > 0, 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(n):
            if model.eval(order_vars[i]).as_long() > 0:
                scheduled.append((model.eval(order_vars[i]).as_long(), i))
        # Sort scheduled meetings by their order value
        scheduled.sort(key=lambda x: x[0])
        
        itinerary = []
        for order_val, i in scheduled:
            start_time = model.eval(start_vars[i]).as_long()
            end_time   = model.eval(end_vars[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()