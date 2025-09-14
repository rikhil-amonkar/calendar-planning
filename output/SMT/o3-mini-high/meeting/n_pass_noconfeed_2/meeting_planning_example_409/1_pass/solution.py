from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Friend meeting data:
    # Times are in minutes since midnight.
    # 9:00 AM is 540.
    friends = [
        {"name": "Thomas", "location": "Bayview", "avail_start": 15 * 60 + 30, "avail_end": 18 * 60 + 30, "min_duration": 120},
        {"name": "Stephanie", "location": "Golden Gate Park", "avail_start": 18 * 60 + 30, "avail_end": 21 * 60 + 45, "min_duration": 30},
        {"name": "Laura", "location": "Nob Hill", "avail_start": 8 * 60 + 45, "avail_end": 16 * 60 + 15, "min_duration": 30},
        {"name": "Betty", "location": "Marina District", "avail_start": 18 * 60 + 45, "avail_end": 21 * 60 + 45, "min_duration": 45},
        {"name": "Patricia", "location": "Embarcadero", "avail_start": 17 * 60 + 30, "avail_end": 22 * 60, "min_duration": 45}
    ]
    n = len(friends)

    # Travel times from Fisherman's Wharf to each location (in minutes)
    fw_travel = {
        "Bayview": 26,
        "Golden Gate Park": 25,
        "Nob Hill": 11,
        "Marina District": 9,
        "Embarcadero": 8
    }

    # Travel times between locations (non-symmetric)
    travel = {
        "Fisherman's Wharf": {"Bayview": 26, "Golden Gate Park": 25, "Nob Hill": 11, "Marina District": 9, "Embarcadero": 8},
        "Bayview": {"Fisherman's Wharf": 25, "Golden Gate Park": 22, "Nob Hill": 20, "Marina District": 25, "Embarcadero": 19},
        "Golden Gate Park": {"Fisherman's Wharf": 24, "Bayview": 23, "Nob Hill": 20, "Marina District": 16, "Embarcadero": 25},
        "Nob Hill": {"Fisherman's Wharf": 11, "Bayview": 19, "Golden Gate Park": 17, "Marina District": 11, "Embarcadero": 9},
        "Marina District": {"Fisherman's Wharf": 10, "Bayview": 27, "Golden Gate Park": 18, "Nob Hill": 12, "Embarcadero": 14},
        "Embarcadero": {"Fisherman's Wharf": 6, "Bayview": 21, "Golden Gate Park": 25, "Nob Hill": 10, "Marina District": 12}
    }

    # Starting time and location: arrive at Fisherman's Wharf at 9:00 (540 minutes)
    start_time_fw = 540

    # Create an Optimize object
    opt = Optimize()

    # Define decision variables for each friend:
    # sel[i] is a Bool indicating if we meet friend i.
    # order[i] is an integer representing the order position if friend i is met;
    # if not met, we set order[i] = -1.
    # start_vars and end_vars are meeting start and end times (in minutes since midnight).
    sel_vars = [Bool(f"sel_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]

    for i in range(n):
        f = friends[i]
        # If friend i is met, meeting start/end must be within availability and last at least the minimum duration.
        opt.add(If(sel_vars[i],
                   And(start_vars[i] >= f["avail_start"],
                       end_vars[i] <= f["avail_end"],
                       end_vars[i] - start_vars[i] >= f["min_duration"],
                       end_vars[i] >= start_vars[i]),
                   True))
        # Enforce order bounds: if selected, order is between 0 and n-1; if not, order is set to -1.
        opt.add(If(sel_vars[i],
                   And(order_vars[i] >= 0, order_vars[i] < n),
                   order_vars[i] == -1))

    # Constraint for the first meeting in the order:
    # If friend i is selected and its order is 0, then we must be able to travel from Fisherman's Wharf.
    for i in range(n):
        f = friends[i]
        opt.add(Implies(And(sel_vars[i], order_vars[i] == 0),
                        start_vars[i] >= start_time_fw + fw_travel[f["location"]]))

    # For every pair of distinct friends, if both are met and friend i is scheduled before friend j,
    # then friend j's meeting must start after friend i's meeting plus travel time between their locations.
    for i in range(n):
        for j in range(n):
            if i != j:
                fi = friends[i]
                fj = friends[j]
                travel_time = travel[fi["location"]][fj["location"]]
                opt.add(Implies(And(sel_vars[i], sel_vars[j], order_vars[i] < order_vars[j]),
                                start_vars[j] >= end_vars[i] + travel_time))

    # Enforce that if two friends are met, their order numbers must be distinct.
    for i in range(n):
        for j in range(i + 1, n):
            opt.add(Implies(And(sel_vars[i], sel_vars[j]), order_vars[i] != order_vars[j]))

    # Our objective is to maximize the number of meetings (friends met)
    opt.maximize(Sum([If(sel_vars[i], 1, 0) for i in range(n)]))

    # Check for a solution and extract the model
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        meetings = []
        for i in range(n):
            if is_true(model[sel_vars[i]]):
                order_val = model[order_vars[i]].as_long()
                st = model[start_vars[i]].as_long()
                en = model[end_vars[i]].as_long()
                meetings.append((order_val, friends[i]["name"], friends[i]["location"], st, en))
        # Sort meetings in order of their scheduled order.
        meetings.sort(key=lambda x: x[0])
        for meeting in meetings:
            _, person, location, st, en = meeting
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(st),
                "end_time": minutes_to_time(en)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # If no schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()