from z3 import *
import json

def minutes_to_str(m):
    # Converts minutes-since-midnight to "HH:MM" 24-hour format.
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    # The starting point: Arriving at Presidio at 9:00 AM (540 minutes from midnight)
    arrival = 540

    # Define the friends’ meeting information.
    # Times are represented in minutes since midnight.
    # For example, 7:15AM is 435, 8:45AM is 525, etc.
    persons = [
        {"name": "Kevin", "location": "Pacific Heights", "avail_start": 435, "avail_end": 525, "duration": 90},
        {"name": "Michelle", "location": "Golden Gate Park", "avail_start": 1200, "avail_end": 1260, "duration": 15},
        {"name": "Emily", "location": "Fisherman's Wharf", "avail_start": 975, "avail_end": 1140, "duration": 30},
        {"name": "Mark", "location": "Marina District", "avail_start": 1095, "avail_end": 1185, "duration": 75},
        {"name": "Barbara", "location": "Alamo Square", "avail_start": 1020, "avail_end": 1140, "duration": 120},
        {"name": "Laura", "location": "Sunset District", "avail_start": 1140, "avail_end": 1275, "duration": 75},
        {"name": "Mary", "location": "Nob Hill", "avail_start": 1050, "avail_end": 1140, "duration": 45},
        {"name": "Helen", "location": "North Beach", "avail_start": 660, "avail_end": 735, "duration": 45}
    ]

    # Define the travel times between locations (in minutes).
    # Note that travel times are not necessarily symmetric.
    travel = {}
    travel[("Presidio", "Pacific Heights")] = 11
    travel[("Presidio", "Golden Gate Park")] = 12
    travel[("Presidio", "Fisherman's Wharf")] = 19
    travel[("Presidio", "Marina District")] = 11
    travel[("Presidio", "Alamo Square")] = 19
    travel[("Presidio", "Sunset District")] = 15
    travel[("Presidio", "Nob Hill")] = 18
    travel[("Presidio", "North Beach")] = 18

    travel[("Pacific Heights", "Presidio")] = 11
    travel[("Pacific Heights", "Golden Gate Park")] = 15
    travel[("Pacific Heights", "Fisherman's Wharf")] = 13
    travel[("Pacific Heights", "Marina District")] = 6
    travel[("Pacific Heights", "Alamo Square")] = 10
    travel[("Pacific Heights", "Sunset District")] = 21
    travel[("Pacific Heights", "Nob Hill")] = 8
    travel[("Pacific Heights", "North Beach")] = 9

    travel[("Golden Gate Park", "Presidio")] = 11
    travel[("Golden Gate Park", "Pacific Heights")] = 16
    travel[("Golden Gate Park", "Fisherman's Wharf")] = 24
    travel[("Golden Gate Park", "Marina District")] = 16
    travel[("Golden Gate Park", "Alamo Square")] = 9
    travel[("Golden Gate Park", "Sunset District")] = 10
    travel[("Golden Gate Park", "Nob Hill")] = 20
    travel[("Golden Gate Park", "North Beach")] = 23

    travel[("Fisherman's Wharf", "Presidio")] = 17
    travel[("Fisherman's Wharf", "Pacific Heights")] = 12
    travel[("Fisherman's Wharf", "Golden Gate Park")] = 25
    travel[("Fisherman's Wharf", "Marina District")] = 9
    travel[("Fisherman's Wharf", "Alamo Square")] = 21
    travel[("Fisherman's Wharf", "Sunset District")] = 27
    travel[("Fisherman's Wharf", "Nob Hill")] = 11
    travel[("Fisherman's Wharf", "North Beach")] = 6

    travel[("Marina District", "Presidio")] = 10
    travel[("Marina District", "Pacific Heights")] = 7
    travel[("Marina District", "Golden Gate Park")] = 18
    travel[("Marina District", "Fisherman's Wharf")] = 10
    travel[("Marina District", "Alamo Square")] = 15
    travel[("Marina District", "Sunset District")] = 19
    travel[("Marina District", "Nob Hill")] = 12
    travel[("Marina District", "North Beach")] = 11

    travel[("Alamo Square", "Presidio")] = 17
    travel[("Alamo Square", "Pacific Heights")] = 10
    travel[("Alamo Square", "Golden Gate Park")] = 9
    travel[("Alamo Square", "Fisherman's Wharf")] = 19
    travel[("Alamo Square", "Marina District")] = 15
    travel[("Alamo Square", "Sunset District")] = 16
    travel[("Alamo Square", "Nob Hill")] = 11
    travel[("Alamo Square", "North Beach")] = 15

    travel[("Sunset District", "Presidio")] = 16
    travel[("Sunset District", "Pacific Heights")] = 21
    travel[("Sunset District", "Golden Gate Park")] = 11
    travel[("Sunset District", "Fisherman's Wharf")] = 29
    travel[("Sunset District", "Marina District")] = 21
    travel[("Sunset District", "Alamo Square")] = 17
    travel[("Sunset District", "Nob Hill")] = 27
    travel[("Sunset District", "North Beach")] = 28

    travel[("Nob Hill", "Presidio")] = 17
    travel[("Nob Hill", "Pacific Heights")] = 8
    travel[("Nob Hill", "Golden Gate Park")] = 17
    travel[("Nob Hill", "Fisherman's Wharf")] = 10
    travel[("Nob Hill", "Marina District")] = 11
    travel[("Nob Hill", "Alamo Square")] = 11
    travel[("Nob Hill", "Sunset District")] = 24
    travel[("Nob Hill", "North Beach")] = 8

    travel[("North Beach", "Presidio")] = 17
    travel[("North Beach", "Pacific Heights")] = 8
    travel[("North Beach", "Golden Gate Park")] = 22
    travel[("North Beach", "Fisherman's Wharf")] = 5
    travel[("North Beach", "Marina District")] = 9
    travel[("North Beach", "Alamo Square")] = 16
    travel[("North Beach", "Sunset District")] = 27
    travel[("North Beach", "Nob Hill")] = 7

    # Create an Optimize object so that we can maximize the number of meetings.
    opt = Optimize()

    n = len(persons)
    sel = [Bool(f"sel_{i}") for i in range(n)]              # Whether to schedule meeting i.
    start_vars = [Int(f"start_{i}") for i in range(n)]         # Meeting starting time (in minutes).
    end_vars = [Int(f"end_{i}") for i in range(n)]             # Meeting ending time.
    order_vars = [Int(f"order_{i}") for i in range(n)]         # The order in which meeting i is visited.

    # Each meeting, if scheduled, must occur within its available window and last at least the required duration.
    for i, p in enumerate(persons):
        opt.add(Implies(sel[i], start_vars[i] >= p["avail_start"]))
        opt.add(Implies(sel[i], end_vars[i] <= p["avail_end"]))
        opt.add(Implies(sel[i], end_vars[i] - start_vars[i] >= p["duration"]))
        # Also, if scheduled, assign a nonnegative order index (and less than n).
        opt.add(Implies(sel[i], order_vars[i] >= 0))
        opt.add(Implies(sel[i], order_vars[i] < n))

    # For any two meetings that are scheduled, enforce distinct order and add travel-time constraints.
    for i in range(n):
        for j in range(i+1, n):
            # If both meetings are selected, their order positions must differ.
            opt.add(Implies(And(sel[i], sel[j]), order_vars[i] != order_vars[j]))
            # If meeting i is scheduled before meeting j, then the start time of j must be at least:
            # (end time of i) + (travel time from i's location to j's location).
            loc_i = persons[i]["location"]
            loc_j = persons[j]["location"]
            travel_ij = travel[(loc_i, loc_j)] if (loc_i, loc_j) in travel else 0
            travel_ji = travel[(loc_j, loc_i)] if (loc_j, loc_i) in travel else 0
            opt.add(Implies(And(sel[i], sel[j], order_vars[i] < order_vars[j]),
                            start_vars[j] >= end_vars[i] + travel_ij))
            # Also, if meeting j comes before meeting i then enforce the reverse travel condition.
            opt.add(Implies(And(sel[i], sel[j], order_vars[j] < order_vars[i]),
                            start_vars[i] >= end_vars[j] + travel_ji))

    # For the first scheduled meeting, ensure that the meeting can be reached from the Presidio.
    for i, p in enumerate(persons):
        loc = p["location"]
        travel_from_presidio = travel[("Presidio", loc)] if ("Presidio", loc) in travel else 0
        opt.add(Implies(And(sel[i], order_vars[i] == 0),
                        start_vars[i] >= arrival + travel_from_presidio))

    # Our objective is to maximize the total number of meetings scheduled.
    total_meetings = Sum([If(sel[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    # Check the model and, if sat, extract the scheduled meetings, sort them by their order value,
    # and output an itinerary as a JSON-formatted dictionary.
    if opt.check() == sat:
        m = opt.model()
        scheduled = []
        for i, p in enumerate(persons):
            if m.evaluate(sel[i]):
                order_val = m.evaluate(order_vars[i]).as_long()
                start_val = m.evaluate(start_vars[i]).as_long()
                end_val = m.evaluate(end_vars[i]).as_long()
                scheduled.append((order_val, p["name"], start_val, end_val))
        scheduled.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, name, start_val, end_val in scheduled:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_str(start_val),
                "end_time": minutes_to_str(end_val)
            })
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()