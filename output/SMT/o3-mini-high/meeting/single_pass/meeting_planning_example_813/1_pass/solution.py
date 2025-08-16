from z3 import *
import json

def main():
    # Define friend data. Times are in minutes from midnight.
    # For example, 9:00AM = 540, 9:45AM = 585, 10:45AM = 645, etc.
    friends = {
        "Joshua":    {"location": "Embarcadero",      "avail_start": 9*60+45,  "avail_end": 18*60,    "min_duration": 105},
        "Jeffrey":   {"location": "Bayview",          "avail_start": 9*60+45,  "avail_end": 20*60+15, "min_duration": 75},
        "Charles":   {"location": "Union Square",     "avail_start": 10*60+45, "avail_end": 20*60+15, "min_duration": 120},
        "Joseph":    {"location": "Chinatown",        "avail_start": 7*60,     "avail_end": 15*60+30, "min_duration": 60},
        "Elizabeth": {"location": "Sunset District",  "avail_start": 9*60,     "avail_end": 9*60+45,  "min_duration": 45},
        "Matthew":   {"location": "Golden Gate Park", "avail_start": 11*60,    "avail_end": 19*60+30, "min_duration": 45},
        "Carol":     {"location": "Financial District", "avail_start": 10*60+45, "avail_end": 11*60+15, "min_duration": 15},
        "Paul":      {"location": "Haight-Ashbury",   "avail_start": 19*60+15, "avail_end": 20*60+30, "min_duration": 15},
        "Rebecca":   {"location": "Mission District", "avail_start": 17*60,    "avail_end": 21*60+45, "min_duration": 45}
    }
    friend_names = list(friends.keys())
    n = len(friend_names)

    # Define travel times in minutes between locations.
    # Each key is a (from, to) tuple.
    travel_times = {
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Mission District"): 20,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Mission District"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 25,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Mission District"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Haight-Ashbury"): 12,
    }

    # Use Optimize so we can maximize the number of meetings.
    opt = Optimize()

    # For each friend, create variables:
    # used[name]: Bool var indicating whether we schedule a meeting with that friend.
    # s[name]: the start time of the meeting (in minutes from midnight).
    # order[name]: an integer order. We use 0 to indicate not scheduled; if scheduled, order > 0.
    used = {}
    s_vars = {}
    order_vars = {}

    for name in friend_names:
        used[name] = Bool(f"used_{name}")
        s_vars[name] = Int(f"s_{name}")
        order_vars[name] = Int(f"order_{name}")

    # Define e[name] as the meeting end time (we assume we use the minimum duration exactly)
    e_vars = {}
    for name in friend_names:
        e_vars[name] = s_vars[name] + friends[name]["min_duration"]

    # Add constraints for each meeting if scheduled.
    for name in friend_names:
        avail_start = friends[name]["avail_start"]
        avail_end = friends[name]["avail_end"]
        min_dur = friends[name]["min_duration"]
        # If meeting is scheduled then:
        #   start time must be within [avail_start, avail_end - min_dur]
        #   order must be > 0.
        opt.add(Implies(used[name], s_vars[name] >= avail_start))
        opt.add(Implies(used[name], s_vars[name] <= avail_end - min_dur))
        opt.add(Implies(used[name], order_vars[name] > 0))
        # If not scheduled, force order to 0.
        opt.add(Implies(Not(used[name]), order_vars[name] == 0))
    
    # For scheduled meetings, force distinct order numbers.
    for i in range(n):
        for j in range(i+1, n):
            name_i = friend_names[i]
            name_j = friend_names[j]
            opt.add(Implies(And(used[name_i], used[name_j]), order_vars[name_i] != order_vars[name_j]))
    
    # Enforce contiguity in the ordering:
    # If any meeting is scheduled with order k+1 then there must be one with order k.
    for k in range(1, n):
        opt.add(If(Sum([If(And(used[name], order_vars[name] == k+1), 1, 0) for name in friend_names]) >= 1,
                   Sum([If(And(used[name], order_vars[name] == k), 1, 0) for name in friend_names]) >= 1,
                   True))
    
    # Define the start state:
    start_time = 9*60  # 9:00AM = 540 minutes
    starting_location = "Marina District"
    # For the very first meeting (order == 1), include travel time from starting location.
    for name in friend_names:
        loc = friends[name]["location"]
        tt = travel_times.get((starting_location, loc), 0)
        opt.add(Implies(order_vars[name] == 1, s_vars[name] >= start_time + tt))
    
    # For consecutive meetings, if meeting j follows meeting i (i.e. order[j] == order[i] + 1)
    # then meeting j must start no earlier than the finish time of i plus travel time.
    for name_i in friend_names:
        for name_j in friend_names:
            if name_i != name_j:
                loc_i = friends[name_i]["location"]
                loc_j = friends[name_j]["location"]
                tt = travel_times.get((loc_i, loc_j), 0)
                opt.add(Implies(And(used[name_i], used[name_j], order_vars[name_j] == order_vars[name_i] + 1),
                                s_vars[name_j] >= e_vars[name_i] + tt))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(used[name], 1, 0) for name in friend_names])
    opt.maximize(total_meetings)
    
    # Solve the optimization problem.
    if opt.check() == sat:
        model = opt.model()
        sol = []
        # Gather scheduled meetings with their order, start and end times.
        for name in friend_names:
            if is_true(model.evaluate(used[name])):
                ord_val = model.evaluate(order_vars[name]).as_long()
                s_val = model.evaluate(s_vars[name]).as_long()
                e_val = s_val + friends[name]["min_duration"]
                sol.append((ord_val, name, s_val, e_val))
        # Sort the meetings in scheduled order.
        sol.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, name, s_val, e_val in sol:
            start_str = f"{s_val//60:02d}:{s_val%60:02d}"
            end_str = f"{e_val//60:02d}:{e_val%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()