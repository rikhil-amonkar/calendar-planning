from z3 import *
import json

def minutes_to_str(m):
    # Convert an integer minute value to a "HH:MM" string.
    h = m // 60
    mins = m % 60
    return f"{h:02d}:{mins:02d}"

def main():
    # Create the Z3 solver instance.
    solver = Solver()

    # Data for each friend:
    # Each friend is available between avail_start and avail_end (in minutes after midnight)
    # and requires at least min_duration minutes of meeting at their specific location.
    # Times: 9:00 is 540, 10:00 is 600, 13:15 is 795, 14:15 is 855, 15:30 is 930,
    # 17:15 is 1035, 18:15 is 1095, 19:30 is 1170, 20:45 is 1245, 21:15 is 1275, 21:30 is 1290.
    friends = [
        { "name": "Rebecca",  "location": "Presidio",         "avail_start": 1095, "avail_end": 1245, "min_duration": 60 },
        { "name": "Linda",    "location": "Sunset District",  "avail_start": 930,  "avail_end": 1185, "min_duration": 30 },
        { "name": "Elizabeth","location": "Haight-Ashbury",   "avail_start": 1035, "avail_end": 1170, "min_duration": 105 },
        { "name": "William",  "location": "Mission District", "avail_start": 795,  "avail_end": 1170, "min_duration": 30 },
        { "name": "Robert",   "location": "Golden Gate Park", "avail_start": 855,  "avail_end": 1290, "min_duration": 45 },
        { "name": "Mark",     "location": "Russian Hill",     "avail_start": 600,  "avail_end": 1275, "min_duration": 75 }
    ]
    n = len(friends)

    # Travel times between locations (in minutes).
    # Note: these are not necessarily symmetric.
    travel = {
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Russian Hill"): 18,

        ("Presidio", "The Castro"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Russian Hill"): 14,

        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Russian Hill"): 24,

        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Russian Hill"): 17,

        ("Mission District", "The Castro"): 7,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Russian Hill"): 15,

        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Russian Hill"): 19,

        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Golden Gate Park"): 21,
    }

    # The starting point is The Castro at 9:00 (540 minutes).
    start_of_day = 540
    initial_location = "The Castro"

    # For each friend, create two Z3 variables:
    #   - start_vars[i]: the meeting start time (in minutes) at friend i's location.
    #   - order_vars[i]: an integer representing the order position in our itinerary.
    start_vars = []
    order_vars = []
    for i in range(n):
        friend = friends[i]
        s = Int(f"start_{i}")
        o = Int(f"order_{i}")
        start_vars.append(s)
        order_vars.append(o)
        # The meeting must start no earlier than their available start and finish (start + meeting duration)
        # before or at the available end.
        solver.add(s >= friend["avail_start"])
        solver.add(s + friend["min_duration"] <= friend["avail_end"])
        # Order must be between 0 and n-1.
        solver.add(o >= 0, o < n)
    
    # All order positions must be distinct.
    solver.add(Distinct(order_vars))

    # Constraint for the first meeting: from the initial location, travel time must be accounted for.
    for i in range(n):
        travel_time = travel[(initial_location, friends[i]["location"])]
        solver.add(Implies(order_vars[i] == 0, start_of_day + travel_time <= start_vars[i]))

    # For any two friends i and j, if friend i is scheduled before friend j, then
    # the finish time of meeting i plus travel time from i's location to j's location must
    # be no later than the start time of meeting j.
    for i in range(n):
        for j in range(n):
            if i != j:
                travel_time = travel[(friends[i]["location"], friends[j]["location"])]
                solver.add(Implies(order_vars[i] < order_vars[j],
                                   start_vars[i] + friends[i]["min_duration"] + travel_time <= start_vars[j]))

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        # Collect schedule entries as tuples: (order, friend index, start time, end time)
        schedule = []
        for i in range(n):
            order_val = model[order_vars[i]].as_long()
            start_val = model[start_vars[i]].as_long()
            end_val = start_val + friends[i]["min_duration"]
            schedule.append((order_val, i, start_val, end_val))
        # Sort the meetings in order.
        schedule.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, i, start_val, end_val in schedule:
            itinerary.append({
                "action": "meet",
                "person": friends[i]["name"],
                "start_time": minutes_to_str(start_val),
                "end_time": minutes_to_str(end_val)
            })
        result = { "itinerary": itinerary }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found!")

if __name__ == "__main__":
    main()