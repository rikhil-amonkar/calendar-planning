import json
from z3 import *

def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def main():
    # Define friend meeting data with available windows (in minutes) and required durations.
    # Times are in minutes from midnight.
    friends = [
        {"name": "David",    "location": "Sunset District",    "avail_start": 9*60+15,   "avail_end": 22*60,    "duration": 15},
        {"name": "Kenneth",  "location": "Union Square",       "avail_start": 21*60+15,  "avail_end": 21*60+45, "duration": 15},
        {"name": "Patricia", "location": "Nob Hill",           "avail_start": 15*60,     "avail_end": 19*60+15, "duration": 120},
        {"name": "Mary",     "location": "Marina District",    "avail_start": 14*60+45,  "avail_end": 16*60+45, "duration": 45},
        {"name": "Charles",  "location": "Richmond District",  "avail_start": 17*60+15,  "avail_end": 21*60,    "duration": 15},
        {"name": "Joshua",   "location": "Financial District", "avail_start": 14*60+30,  "avail_end": 17*60+15, "duration": 90},
        {"name": "Ronald",   "location": "Embarcadero",        "avail_start": 18*60+15,  "avail_end": 20*60+45, "duration": 30},
        {"name": "George",   "location": "The Castro",         "avail_start": 14*60+15,  "avail_end": 19*60,    "duration": 105},
        {"name": "Kimberly", "location": "Alamo Square",       "avail_start": 9*60,      "avail_end": 14*60+30, "duration": 105},
        {"name": "William",  "location": "Presidio",           "avail_start": 7*60,      "avail_end": 12*60+45, "duration": 60}
    ]

    # Travel times (in minutes) between locations.
    travel_times = {
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Presidio"): 16,
        
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Presidio"): 24,
        
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Presidio"): 10,
        
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Presidio"): 7,
        
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Presidio"): 20,
        
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Presidio"): 20,
        
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Presidio"): 17,
        
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Alamo Square"): 19,
    }

    # Number of potential meetings
    n = len(friends)
    solver = Optimize()

    # Decision variables:
    #   chosen[i]: Bool, true if meeting i is scheduled.
    #   s_vars[i]: Int, start time (in minutes) for meeting i (if scheduled).
    #   order_vars[i]: Int, the position in the overall schedule (if scheduled; -1 otherwise).
    chosen = [Bool(f"chosen_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]

    # Add constraints for each meeting.
    for i, friend in enumerate(friends):
        # If meeting is chosen, its start time must lie within its available window.
        solver.add(Or(Not(chosen[i]),
                        And(s_vars[i] >= friend["avail_start"],
                            s_vars[i] <= friend["avail_end"] - friend["duration"])))
        # If chosen, order must be between 0 and n-1.
        solver.add(Or(Not(chosen[i]),
                        And(order_vars[i] >= 0, order_vars[i] < n)))
        # If not chosen, fix order to -1.
        solver.add(Implies(Not(chosen[i]), order_vars[i] == -1))

    # Ensure that if two meetings are scheduled, their order values are distinct.
    for i in range(n):
        for j in range(i+1, n):
            solver.add(Implies(And(chosen[i], chosen[j]), order_vars[i] != order_vars[j]))

    # For the first meeting in the schedule (order == 0), enforce that it is reachable from Russian Hill.
    # Arrival at Russian Hill is at 9:00 (540 minutes).
    for i, friend in enumerate(friends):
        travel_from_start = travel_times.get(("Russian Hill", friend["location"]), 9999)
        solver.add(Implies(And(chosen[i], order_vars[i] == 0),
                           s_vars[i] >= 540 + travel_from_start))

    # Enforce consecutive meeting constraints.
    # If meeting j immediately follows meeting i (i.e. order[j] == order[i] + 1),
    # then the start time of meeting j must be at least the end time of meeting i plus travel time from i to j.
    for i in range(n):
        for j in range(n):
            if i != j:
                travel_ij = travel_times.get((friends[i]["location"], friends[j]["location"]), 9999)
                solver.add(Implies(And(chosen[i], chosen[j], order_vars[j] == order_vars[i] + 1),
                                   s_vars[j] >= s_vars[i] + friends[i]["duration"] + travel_ij))

    # Enforce order consistency: if meeting i is scheduled before meeting j, then s_i <= s_j.
    for i in range(n):
        for j in range(n):
            if i != j:
                solver.add(Implies(And(chosen[i], chosen[j], order_vars[i] < order_vars[j]),
                                   s_vars[i] <= s_vars[j]))

    # Ensure that every scheduled meeting with order > 0 has a predecessor.
    for i in range(n):
        solver.add(Implies(And(chosen[i], order_vars[i] > 0),
                           Or([And(chosen[j], order_vars[j] == order_vars[i] - 1) for j in range(n)])))

    # Objective: maximize the total number of meetings scheduled.
    total_meetings = Sum([If(chosen[i], 1, 0) for i in range(n)])
    solver.maximize(total_meetings)

    if solver.check() == sat:
        model = solver.model()
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(chosen[i])):
                # Append tuple (order value, i) for sorting.
                scheduled.append((model.evaluate(order_vars[i]).as_long(), i))
        scheduled.sort(key=lambda x: x[0])
        
        itinerary = []
        for order_val, i in scheduled:
            start_time = model.evaluate(s_vars[i]).as_long()
            end_time = start_time + friends[i]["duration"]
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
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()