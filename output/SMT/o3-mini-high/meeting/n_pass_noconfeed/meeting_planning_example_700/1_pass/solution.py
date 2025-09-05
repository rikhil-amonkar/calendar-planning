from z3 import *
import json

def to_time_str(t):
    # t is minutes from midnight; returns H:MM with no leading zero for hour.
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Arrival: You arrive at Presidio at 9:00 (540 minutes after midnight)
    arrival_time = 9 * 60

    # Define friends' meeting information.
    # Times are in minutes from midnight.
    friends = [
        {"name": "Kevin", "location": "Pacific Heights", "avail_start": 7 * 60 + 15, "avail_end": 8 * 60 + 45, "min_duration": 90},
        {"name": "Michelle", "location": "Golden Gate Park", "avail_start": 20 * 60, "avail_end": 21 * 60, "min_duration": 15},
        {"name": "Emily", "location": "Fisherman's Wharf", "avail_start": 16 * 60 + 15, "avail_end": 19 * 60, "min_duration": 30},
        {"name": "Mark", "location": "Marina District", "avail_start": 18 * 60 + 15, "avail_end": 19 * 60 + 45, "min_duration": 75},
        {"name": "Barbara", "location": "Alamo Square", "avail_start": 17 * 60, "avail_end": 19 * 60, "min_duration": 120},
        {"name": "Laura", "location": "Sunset District", "avail_start": 19 * 60, "avail_end": 21 * 60 + 15, "min_duration": 75},
        {"name": "Mary", "location": "Nob Hill", "avail_start": 17 * 60 + 30, "avail_end": 19 * 60, "min_duration": 45},
        {"name": "Helen", "location": "North Beach", "avail_start": 11 * 60, "avail_end": 12 * 60 + 15, "min_duration": 45}
    ]
    n = len(friends)

    # Define travel times (in minutes) between locations.
    # Keys are (origin, destination)
    travel = {
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,

        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "North Beach"): 9,

        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "North Beach"): 23,

        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,

        ("Marina District", "Presidio"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "North Beach"): 11,

        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,

        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "North Beach"): 28,

        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "North Beach"): 8,

        ("North Beach", "Presidio"): 17,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Nob Hill"): 7,
    }

    # Create an Optimize object
    opt = Optimize()

    # Decision variables for each friend:
    # selected[i] is True if meeting with friend i is scheduled.
    # s[i] and e[i] represent the start and end times of the meeting.
    # order[i] is an integer indicating the position in the sequence; if not selected, we set order to -1.
    selected = [Bool(f"sel_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]
    order_vars = [Int(f"ord_{i}") for i in range(n)]

    for i, f in enumerate(friends):
        # If not selected, force order to be -1.
        opt.add(Implies(Not(selected[i]), order_vars[i] == -1))
        # If selected, order must be between 0 and n-1.
        opt.add(Implies(selected[i], And(order_vars[i] >= 0, order_vars[i] < n)))
        # Meeting must be within the friend available window.
        opt.add(Implies(selected[i], s_vars[i] >= f["avail_start"]))
        opt.add(Implies(selected[i], e_vars[i] <= f["avail_end"]))
        # Meeting duration must be at least the minimum required.
        opt.add(Implies(selected[i], e_vars[i] - s_vars[i] >= f["min_duration"]))
        # Additionally, keep times in a reasonable range.
        opt.add(s_vars[i] >= 0, e_vars[i] <= 24 * 60)

    # For every two distinct friends that are both scheduled, enforce a total order and travel constraints.
    for i in range(n):
        for j in range(i + 1, n):
            # If both meetings are selected, their order numbers must be different.
            opt.add(Implies(And(selected[i], selected[j]), order_vars[i] != order_vars[j]))
            # If friend i is scheduled before friend j, then meeting j cannot start until after meeting i finishes plus travel time.
            travel_ij = travel.get((friends[i]["location"], friends[j]["location"]))
            travel_ji = travel.get((friends[j]["location"], friends[i]["location"]))
            # It is assumed the travel times exist in the dictionary.
            opt.add(Implies(And(selected[i], selected[j], order_vars[i] < order_vars[j]),
                            s_vars[j] >= e_vars[i] + travel_ij))
            opt.add(Implies(And(selected[i], selected[j], order_vars[i] > order_vars[j]),
                            s_vars[i] >= e_vars[j] + travel_ji))

    # For any scheduled meeting that is the first in order (order == 0),
    # ensure that its start time is after traveling from the Presidio.
    for i in range(n):
        travel_from_presidio = travel.get(("Presidio", friends[i]["location"]))
        if travel_from_presidio is None:
            travel_from_presidio = 0
        opt.add(Implies(And(selected[i], order_vars[i] == 0),
                        s_vars[i] >= arrival_time + travel_from_presidio))

    # Objective: maximize the number of scheduled meetings.
    total_selected = Sum([If(selected[i], 1, 0) for i in range(n)])
    opt.maximize(total_selected)

    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        # Gather scheduled meetings with their order.
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(selected[i])):
                ord_val = model.evaluate(order_vars[i]).as_long()
                scheduled.append((ord_val, i))
        # Sort meetings in the order they occur.
        scheduled.sort(key=lambda x: x[0])
        itinerary = []
        for ord_val, i in scheduled:
            start_val = model.evaluate(s_vars[i]).as_long()
            end_val = model.evaluate(e_vars[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": to_time_str(start_val),
                "end_time": to_time_str(end_val)
            })
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()