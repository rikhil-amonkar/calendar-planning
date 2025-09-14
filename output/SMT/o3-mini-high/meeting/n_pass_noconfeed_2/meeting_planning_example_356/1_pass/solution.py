import json
from z3 import *

def minutes_to_str(t):
    hr = t // 60
    mn = t % 60
    return f"{hr}:{mn:02d}"

def main():
    # Travel times in minutes
    travel_times = {
        "Bayview": {"North Beach": 21, "Presidio": 31, "Haight-Ashbury": 19, "Union Square": 17},
        "North Beach": {"Bayview": 22, "Presidio": 17, "Haight-Ashbury": 18, "Union Square": 7},
        "Presidio": {"Bayview": 31, "North Beach": 18, "Haight-Ashbury": 15, "Union Square": 22},
        "Haight-Ashbury": {"Bayview": 18, "North Beach": 19, "Presidio": 15, "Union Square": 17},
        "Union Square": {"Bayview": 15, "North Beach": 10, "Presidio": 24, "Haight-Ashbury": 18}
    }

    # Friend meeting parameters
    # Times expressed in minutes from midnight.
    # 9:00 AM = 540, 7:45 AM = 465, etc.
    friends = {
        "Barbara": {
            "location": "North Beach",
            "avail_start": 13 * 60 + 45,  # 13:45 = 825
            "avail_end": 20 * 60 + 15,    # 20:15 = 1215
            "min_duration": 60
        },
        "Margaret": {
            "location": "Presidio",
            "avail_start": 10 * 60 + 15,  # 10:15 = 615
            "avail_end": 15 * 60 + 15,    # 15:15 = 915
            "min_duration": 30
        },
        "Kevin": {
            "location": "Haight-Ashbury",
            "avail_start": 20 * 60,       # 20:00 = 1200
            "avail_end": 20 * 60 + 45,    # 20:45 = 1245
            "min_duration": 30
        },
        "Kimberly": {
            "location": "Union Square",
            "avail_start": 7 * 60 + 45,   # 7:45 = 465
            "avail_end": 16 * 60 + 45,    # 16:45 = 1005
            "min_duration": 30
        }
    }

    # Starting point details
    start_location = "Bayview"
    start_time = 9 * 60  # 9:00 AM is 540 minutes

    # Create an optimization solver
    opt = Optimize()

    # Decision variables for each friend:
    # s: meeting start time, e: meeting end time, order: order in the itinerary, chosen: whether to meet
    s_vars = {}
    e_vars = {}
    order_vars = {}
    chosen_vars = {}

    for name, params in friends.items():
        s_vars[name] = Int(f"s_{name}")
        e_vars[name] = Int(f"e_{name}")
        order_vars[name] = Int(f"order_{name}")
        chosen_vars[name] = Bool(f"chosen_{name}")

        avail_start = params["avail_start"]
        avail_end = params["avail_end"]
        min_duration = params["min_duration"]

        # If meeting is chosen, enforce meeting window and duration.
        opt.add(If(chosen_vars[name], s_vars[name] >= avail_start, s_vars[name] == 0))
        opt.add(If(chosen_vars[name], e_vars[name] <= avail_end, e_vars[name] == 0))
        opt.add(If(chosen_vars[name], e_vars[name] - s_vars[name] >= min_duration, e_vars[name] == 0))
        # For ordering: if chosen, order must be between 0 and 3; if not, set to -1.
        opt.add(If(chosen_vars[name], And(order_vars[name] >= 0, order_vars[name] <= 3), order_vars[name] == -1))

    friend_names = list(friends.keys())
    n = len(friend_names)

    # Ensure that if two meetings are chosen, they have distinct order numbers.
    for i in range(n):
        for j in range(i+1, n):
            f1 = friend_names[i]
            f2 = friend_names[j]
            opt.add(Implies(And(chosen_vars[f1], chosen_vars[f2]), order_vars[f1] != order_vars[f2]))

    # Travel constraints:
    # 1. For the first meeting in the itinerary, account for travel from start location.
    for name, params in friends.items():
        loc = params["location"]
        travel_from_start = travel_times[start_location][loc]
        opt.add(Implies(And(chosen_vars[name], order_vars[name] == 0),
                        s_vars[name] >= start_time + travel_from_start))

    # 2. For every pair of chosen meetings, enforce that if one comes before the other,
    # then the travel time between the locations is respected.
    for i in range(n):
        for j in range(n):
            if i != j:
                f1 = friend_names[i]
                f2 = friend_names[j]
                loc1 = friends[f1]["location"]
                loc2 = friends[f2]["location"]
                travel_time_fg = travel_times[loc1][loc2]
                opt.add(Implies(And(chosen_vars[f1], chosen_vars[f2], order_vars[f1] < order_vars[f2]),
                                s_vars[f2] >= e_vars[f1] + travel_time_fg))

    # Objective: maximize the total number of meetings scheduled
    total_meetings = Sum([If(chosen_vars[name], 1, 0) for name in friend_names])
    opt.maximize(total_meetings)

    # Check for a solution
    if opt.check() == sat:
        mod = opt.model()
        # Gather scheduled meetings with their order
        scheduled = []
        for name in friend_names:
            if is_true(mod[chosen_vars[name]]):
                scheduled.append((mod[order_vars[name]].as_long(), name))
        scheduled.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, name in scheduled:
            start_val = mod[s_vars[name]].as_long()
            end_val = mod[e_vars[name]].as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[name]["location"],
                "person": name,
                "start_time": minutes_to_str(start_val),
                "end_time": minutes_to_str(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()