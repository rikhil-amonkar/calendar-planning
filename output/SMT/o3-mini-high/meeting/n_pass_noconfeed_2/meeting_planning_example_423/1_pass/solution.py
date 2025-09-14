from z3 import *
import json

def minutes_to_time_string(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times (in minutes) between locations.
    travel = {
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Union Square"): 22,

        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Union Square"): 21,

        ("North Beach", "Presidio"): 17,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Union Square"): 7,

        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Union Square"): 9,

        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,

        ("Union Square", "Presidio"): 24,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22,
    }
    
    # Friend meeting parameters.
    # Times are in minutes from midnight.
    # 9:00 AM = 540, 8:45 PM = 20*60+45 = 1245, etc.
    friends = [
        {
            "name": "Jason",
            "location": "Richmond District",
            "avail_start": 780,    # 13:00
            "avail_end": 1245,     # 20:45
            "min_duration": 90
        },
        {
            "name": "Melissa",
            "location": "North Beach",
            "avail_start": 1125,   # 18:45
            "avail_end": 1215,     # 20:15
            "min_duration": 45
        },
        {
            "name": "Brian",
            "location": "Financial District",
            "avail_start": 585,    # 9:45
            "avail_end": 1305,     # 21:45
            "min_duration": 15
        },
        {
            "name": "Elizabeth",
            "location": "Golden Gate Park",
            "avail_start": 525,    # 8:45
            "avail_end": 1290,     # 21:30
            "min_duration": 105
        },
        {
            "name": "Laura",
            "location": "Union Square",
            "avail_start": 855,    # 14:15
            "avail_end": 1170,     # 19:30
            "min_duration": 75
        }
    ]
    
    n = len(friends)
    
    # Create an Optimize instance.
    opt = Optimize()

    # Decision variables:
    # For each friend meeting i:
    #   start_vars[i]: meeting start time in minutes.
    #   end_vars[i]: meeting end time in minutes. (We fix meeting duration = min_duration)
    #   order_vars[i]: position in the visit order if scheduled (0 means first, 1 second, etc.)
    #   scheduled[i]: Boolean indicator if meeting i is scheduled.
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars   = [Int(f"end_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]
    scheduled  = [Bool(f"scheduled_{i}") for i in range(n)]
    
    # Add constraints for each meeting.
    for i, friend in enumerate(friends):
        # If meeting is scheduled then it must occur within the friend's availability window.
        opt.add(Implies(scheduled[i], start_vars[i] >= friend["avail_start"]))
        opt.add(Implies(scheduled[i], start_vars[i] <= friend["avail_end"] - friend["min_duration"]))
        opt.add(Implies(scheduled[i], end_vars[i] == start_vars[i] + friend["min_duration"]))
        # When not scheduled, set order to -1.
        opt.add(Implies(scheduled[i], And(order_vars[i] >= 0, order_vars[i] < n)))
        opt.add(Implies(Not(scheduled[i]), order_vars[i] == -1))
        
        # For the first meeting in the sequence, include travel time from Presidio.
        travel_from_presidio = travel[("Presidio", friend["location"])]
        opt.add(Implies(And(scheduled[i], order_vars[i] == 0), start_vars[i] >= 540 + travel_from_presidio))
    
    # Distinct order numbers for scheduled meetings.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))
    
    # Add ordering constraints based on travel times between meetings.
    # If meeting i comes before meeting j then meeting j must start after meeting i ends plus travel time from i to j.
    for i in range(n):
        for j in range(n):
            if i != j:
                travel_time = travel[(friends[i]["location"], friends[j]["location"])]
                opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                                start_vars[j] >= end_vars[i] + travel_time))
    
    # Objective: maximize number of scheduled meetings.
    count_meetings = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    h1 = opt.maximize(count_meetings)
    # Secondary objective: minimize the sum of start times (to avoid unnecessary delays).
    h2 = opt.minimize(Sum([If(scheduled[i], start_vars[i], 0) for i in range(n)]))
    
    # Solve the optimization problem.
    if opt.check() == sat:
        mod = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if is_true(mod.evaluate(scheduled[i])):
                meeting = {
                    "name": friends[i]["name"],
                    "location": friends[i]["location"],
                    "start": mod.evaluate(start_vars[i]).as_long(),
                    "end": mod.evaluate(end_vars[i]).as_long(),
                    "order": mod.evaluate(order_vars[i]).as_long()
                }
                scheduled_meetings.append(meeting)
        # Sort meetings by their order in the schedule.
        scheduled_meetings.sort(key=lambda x: x["order"])
        
        itinerary = []
        for m in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["name"],
                "start_time": minutes_to_time_string(m["start"]),
                "end_time": minutes_to_time_string(m["end"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()