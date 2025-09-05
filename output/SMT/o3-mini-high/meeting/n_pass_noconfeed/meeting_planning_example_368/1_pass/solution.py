from z3 import *
import json

def minutes_to_time(m):
    # Convert minutes from midnight to "H:MM" 24-hour format (no leading zero for hour)
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times (in minutes) between locations
    travel_times = {
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Financial District"): 19,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Financial District"): 11,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Russian Hill"): 10,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "North Beach"): 7,
    }

    # Friend meeting details
    # Times are in minutes from midnight.
    # Joseph: available from 8:30 (510) to 19:15 (1155), minimum meeting 60 minutes, location Russian Hill.
    # Nancy: available from 11:00 (660) to 16:00 (960), minimum meeting 90 minutes, location Alamo Square.
    # Jason: available from 16:45 (1005) to 21:45 (1305), minimum meeting 15 minutes, location North Beach.
    # Jeffrey: available from 10:30 (630) to 15:45 (945), minimum meeting 45 minutes, location Financial District.
    friends = [
        {"person": "Joseph", "location": "Russian Hill", "avail_start": 510, "avail_end": 1155, "min_duration": 60},
        {"person": "Nancy", "location": "Alamo Square", "avail_start": 660, "avail_end": 960, "min_duration": 90},
        {"person": "Jason", "location": "North Beach", "avail_start": 1005, "avail_end": 1305, "min_duration": 15},
        {"person": "Jeffrey", "location": "Financial District", "avail_start": 630, "avail_end": 945, "min_duration": 45}
    ]
    
    n = len(friends)
    # You arrive at Bayview at 9:00 (540 minutes)
    start_time_bayview = 540

    # Create optimization instance
    opt = Optimize()

    # Decision variables:
    # x[i]: whether to schedule meeting with friend i (Bool)
    # S[i]: start time (in minutes) of meeting with friend i (Int)
    # E[i]: end time (in minutes) of meeting with friend i (Int)
    # order[i]: ordering position (0 if not scheduled, otherwise an integer between 1 and n)
    x = [Bool(f"x_{i}") for i in range(n)]
    S_vars = [Int(f"S_{i}") for i in range(n)]
    E_vars = [Int(f"E_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]

    # Sum of scheduled meetings (for ordering upper bounds)
    total_meetings = Sum([If(x[i], 1, 0) for i in range(n)])

    # Add constraints for each friend meeting's time and ordering
    for i in range(n):
        friend = friends[i]
        # If meeting is scheduled, its start & end must be within friend's availability and satisfy minimum duration.
        opt.add(Implies(x[i], S_vars[i] >= friend["avail_start"]))
        opt.add(Implies(x[i], E_vars[i] <= friend["avail_end"]))
        opt.add(Implies(x[i], E_vars[i] - S_vars[i] >= friend["min_duration"]))
        # For unscheduled meetings, set order to 0.
        opt.add(Implies(Not(x[i]), order_vars[i] == 0))
        # If scheduled, order must be at least 1 and no more than the total number of meetings scheduled.
        opt.add(Implies(x[i], And(order_vars[i] >= 1, order_vars[i] <= total_meetings)))

    # Enforce that scheduled meetings have distinct order values.
    for i in range(n):
        for j in range(i + 1, n):
            opt.add(Implies(And(x[i], x[j]), order_vars[i] != order_vars[j]))

    # Enforce that orders are contiguous.
    # For each r from 1 to n, if total meetings scheduled is at least r, then some meeting has order equal to r.
    for r in range(1, n + 1):
        opt.add(Implies(total_meetings >= r, Or([order_vars[i] == r for i in range(n)])))

    # For the first meeting in the itinerary (order == 1), ensure arrival from Bayview is respected.
    for i in range(n):
        loc = friends[i]["location"]
        travel_from_bayview = travel_times[("Bayview", loc)]
        opt.add(Implies(And(x[i], order_vars[i] == 1), S_vars[i] >= start_time_bayview + travel_from_bayview))

    # For adjacent meetings, enforce travel-time constraints.
    for i in range(n):
        for j in range(n):
            if i != j:
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                travel_ij = travel_times[(loc_i, loc_j)]
                # If meeting j immediately follows meeting i, then S[j] must be at least E[i] plus travel time.
                opt.add(Implies(And(x[i], x[j], order_vars[j] == order_vars[i] + 1),
                                S_vars[j] >= E_vars[i] + travel_ij))

    # Objective: maximize the number of meetings scheduled.
    opt.maximize(total_meetings)

    # Check for a solution.
    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if m.evaluate(x[i]):
                ord_val = m.evaluate(order_vars[i]).as_long()
                start_val = m.evaluate(S_vars[i]).as_long()
                end_val = m.evaluate(E_vars[i]).as_long()
                scheduled_meetings.append((ord_val, friends[i]["person"], friends[i]["location"], start_val, end_val))
        # Sort meetings by their scheduled order.
        scheduled_meetings.sort(key=lambda tup: tup[0])
        itinerary = []
        for order_val, person, location, start_val, end_val in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # No feasible schedule found.
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == '__main__':
    main()