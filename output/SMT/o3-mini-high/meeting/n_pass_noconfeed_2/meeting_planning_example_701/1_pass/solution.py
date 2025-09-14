from z3 import *
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times (in minutes) between locations.
    travel_times = {
        "Mission District": {
            "The Castro": 7,
            "Nob Hill": 12,
            "Presidio": 25,
            "Marina District": 19,
            "Pacific Heights": 16,
            "Golden Gate Park": 17,
            "Chinatown": 16,
            "Richmond District": 20
        },
        "The Castro": {
            "Mission District": 7,
            "Nob Hill": 16,
            "Presidio": 20,
            "Marina District": 21,
            "Pacific Heights": 16,
            "Golden Gate Park": 11,
            "Chinatown": 22,
            "Richmond District": 16
        },
        "Nob Hill": {
            "Mission District": 13,
            "The Castro": 17,
            "Presidio": 17,
            "Marina District": 11,
            "Pacific Heights": 8,
            "Golden Gate Park": 17,
            "Chinatown": 6,
            "Richmond District": 14
        },
        "Presidio": {
            "Mission District": 26,
            "The Castro": 21,
            "Nob Hill": 18,
            "Marina District": 11,
            "Pacific Heights": 11,
            "Golden Gate Park": 12,
            "Chinatown": 21,
            "Richmond District": 7
        },
        "Marina District": {
            "Mission District": 20,
            "The Castro": 22,
            "Nob Hill": 12,
            "Presidio": 10,
            "Pacific Heights": 7,
            "Golden Gate Park": 18,
            "Chinatown": 15,
            "Richmond District": 11
        },
        "Pacific Heights": {
            "Mission District": 15,
            "The Castro": 16,
            "Nob Hill": 8,
            "Presidio": 11,
            "Marina District": 6,
            "Golden Gate Park": 15,
            "Chinatown": 11,
            "Richmond District": 12
        },
        "Golden Gate Park": {
            "Mission District": 17,
            "The Castro": 13,
            "Nob Hill": 20,
            "Presidio": 11,
            "Marina District": 16,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Richmond District": 7
        },
        "Chinatown": {
            "Mission District": 17,
            "The Castro": 22,
            "Nob Hill": 9,
            "Presidio": 19,
            "Marina District": 12,
            "Pacific Heights": 10,
            "Golden Gate Park": 23,
            "Richmond District": 20
        },
        "Richmond District": {
            "Mission District": 20,
            "The Castro": 16,
            "Nob Hill": 17,
            "Presidio": 7,
            "Marina District": 9,
            "Pacific Heights": 10,
            "Golden Gate Park": 9,
            "Chinatown": 20
        }
    }

    # Friend meeting details: each friend has a meeting location, an availability window (in minutes from midnight)
    # and a minimum meeting duration.
    # Times are converted as follows:
    # 9:00 AM = 540, 7:15 PM = 19*60+15 = 1155, 9:15 PM = 1275, 10:15 PM = 1335, etc.
    friends = [
        {"name": "Lisa", "location": "The Castro", "avail_start": 1155, "avail_end": 1275, "min_duration": 120},
        {"name": "Daniel", "location": "Nob Hill", "avail_start": 495, "avail_end": 660, "min_duration": 15},
        {"name": "Elizabeth", "location": "Presidio", "avail_start": 1275, "avail_end": 1335, "min_duration": 45},
        {"name": "Steven", "location": "Marina District", "avail_start": 990, "avail_end": 1245, "min_duration": 90},
        {"name": "Timothy", "location": "Pacific Heights", "avail_start": 720, "avail_end": 1080, "min_duration": 90},
        {"name": "Ashley", "location": "Golden Gate Park", "avail_start": 1245, "avail_end": 1305, "min_duration": 60},
        {"name": "Kevin", "location": "Chinatown", "avail_start": 720, "avail_end": 1140, "min_duration": 30},
        {"name": "Betty", "location": "Richmond District", "avail_start": 795, "avail_end": 945, "min_duration": 30}
    ]

    n = len(friends)
    opt = Optimize()

    # Decision variables for each friend meeting.
    # x[i] indicates whether we meet friend i.
    x = [Bool(f"x_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]
    
    # For each friend meeting, if chosen, meeting time must be within the available window and last at least the minimum duration.
    for i, friend in enumerate(friends):
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_dur = friend["min_duration"]
        opt.add(Implies(x[i], start_vars[i] >= avail_start))
        opt.add(Implies(x[i], end_vars[i] <= avail_end))
        opt.add(Implies(x[i], end_vars[i] - start_vars[i] >= min_dur))
        # If not scheduled, fix the order to n (which is outside the range for scheduled meetings).
        opt.add(Implies(Not(x[i]), order_vars[i] == n))
        # If scheduled, order must be in the range 0...n-1.
        opt.add(Implies(x[i], And(order_vars[i] >= 0, order_vars[i] < n)))
    
    # Ensure that scheduled meetings get distinct order values.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(x[i], x[j]), order_vars[i] != order_vars[j]))
    
    # Add travel constraints: if meeting i is scheduled before meeting j,
    # then the start time of meeting j must be at least the end time of meeting i plus the travel time.
    for i in range(n):
        for j in range(n):
            if i != j:
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                t_time = travel_times[loc_i][loc_j]
                opt.add(Implies(And(x[i], x[j], order_vars[i] < order_vars[j]),
                                start_vars[j] >= end_vars[i] + t_time))
    
    # The first meeting (i.e. order==0) must be reachable from Mission District,
    # where you arrive at 9:00 (540 minutes).
    for i in range(n):
        loc = friends[i]["location"]
        t_time = travel_times["Mission District"][loc]
        opt.add(Implies(And(x[i], order_vars[i] == 0),
                        start_vars[i] >= 540 + t_time))
    
    # Objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(x[i], 1, 0) for i in range(n)]))
    
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(x[i])):
                ord_val = model.evaluate(order_vars[i]).as_long()
                s_time = model.evaluate(start_vars[i]).as_long()
                e_time = model.evaluate(end_vars[i]).as_long()
                scheduled.append((ord_val, i, s_time, e_time))
        # Sort the scheduled meetings by their order.
        scheduled.sort(key=lambda tup: tup[0])
        itinerary = []
        for _, i, s_time, e_time in scheduled:
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": minutes_to_time(s_time),
                "end_time": minutes_to_time(e_time)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()