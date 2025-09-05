import json
from z3 import *

def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def main():
    # Define travel time data (in minutes) as provided.
    travel_times = {
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Sunset District"): 17,

        ("Marina District", "The Castro"): 22,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Sunset District"): 19,

        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Sunset District"): 15,

        ("North Beach", "The Castro"): 23,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Sunset District"): 27,

        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Sunset District"): 30,

        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Sunset District"): 15,

        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Sunset District"): 10,

        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Sunset District"): 11,

        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Sunset District"): 16,

        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Sunset District"): 30,

        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
    }
    
    # Define friends and their meeting constraints.
    # Times are represented in minutes from midnight.
    # Arrival at "The Castro" is fixed at 9:00 -> 540 minutes.
    friends = [
        {"name": "Elizabeth", "location": "Marina District", "avail_start": 1140, "avail_end": 1245, "min_duration": 105},
        {"name": "Joshua", "location": "Presidio", "avail_start": 510, "avail_end": 795, "min_duration": 105},
        {"name": "Timothy", "location": "North Beach", "avail_start": 1185, "avail_end": 1320, "min_duration": 90},
        {"name": "David", "location": "Embarcadero", "avail_start": 645, "avail_end": 750, "min_duration": 30},
        {"name": "Kimberly", "location": "Haight-Ashbury", "avail_start": 1005, "avail_end": 1290, "min_duration": 75},
        {"name": "Lisa", "location": "Golden Gate Park", "avail_start": 1050, "avail_end": 1305, "min_duration": 45},
        {"name": "Ronald", "location": "Richmond District", "avail_start": 480, "avail_end": 570, "min_duration": 90},
        {"name": "Stephanie", "location": "Alamo Square", "avail_start": 930, "avail_end": 990, "min_duration": 30},
        {"name": "Helen", "location": "Financial District", "avail_start": 1050, "avail_end": 1110, "min_duration": 45},
        {"name": "Laura", "location": "Sunset District", "avail_start": 1065, "avail_end": 1275, "min_duration": 90},
    ]

    n = len(friends)
    # Use M_val as a sentinel value for order when a meeting is not selected.
    M_val = n

    opt = Optimize()

    # Create SMT variables for each friend:
    #   start time, end time, order position, and a Boolean indicating whether the meeting is scheduled.
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]
    selected_vars = [Bool(f"selected_{i}") for i in range(n)]

    # Add constraints for each meeting based on availability and minimum meeting duration.
    for i, friend in enumerate(friends):
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_duration = friend["min_duration"]
        opt.add(Implies(selected_vars[i], start_vars[i] >= avail_start))
        opt.add(Implies(selected_vars[i], end_vars[i] <= avail_end))
        opt.add(Implies(selected_vars[i], end_vars[i] - start_vars[i] >= min_duration))
        # If selected, the order must be in [0, M_val - 1]; if not, set the order to the sentinel M_val.
        opt.add(Implies(selected_vars[i], And(order_vars[i] >= 0, order_vars[i] < M_val)))
        opt.add(Implies(Not(selected_vars[i]), order_vars[i] == M_val))

    # Ensure that if at least one meeting is scheduled, one of them is the first (order 0).
    opt.add(Implies(Sum([If(selected_vars[i], 1, 0) for i in range(n)]) > 0,
                    Or([And(selected_vars[i], order_vars[i] == 0) for i in range(n)])))

    # For every pair of meetings that are both scheduled, enforce distinct order values
    # and the travel time constraints between them.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(selected_vars[i], selected_vars[j]), order_vars[i] != order_vars[j]))
            opt.add(Implies(And(selected_vars[i], selected_vars[j], order_vars[i] < order_vars[j]),
                            end_vars[i] + travel_times[(friends[i]["location"], friends[j]["location"])] <= start_vars[j]))
            opt.add(Implies(And(selected_vars[i], selected_vars[j], order_vars[j] < order_vars[i]),
                            end_vars[j] + travel_times[(friends[j]["location"], friends[i]["location"])] <= start_vars[i]))

    # For the first selected meeting, add the constraint that you must account for travel
    # from your initial arrival location ("The Castro" at 9:00 -> 540).
    for i in range(n):
        opt.add(Implies(And(selected_vars[i], order_vars[i] == 0),
                        540 + travel_times[("The Castro", friends[i]["location"])] <= start_vars[i]))

    # Objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(selected_vars[i], 1, 0) for i in range(n)]))

    if opt.check() == sat:
        model = opt.model()
        # Collect the meetings that were scheduled along with their order.
        scheduled = []
        for i in range(n):
            if model.evaluate(selected_vars[i]):
                order_val = model.evaluate(order_vars[i]).as_long()
                s_time = model.evaluate(start_vars[i]).as_long()
                e_time = model.evaluate(end_vars[i]).as_long()
                scheduled.append((order_val, i, s_time, e_time))
        # Sort the scheduled meetings by their order.
        scheduled.sort(key=lambda x: x[0])
        itinerary = []
        for _, i, s_time, e_time in scheduled:
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": minutes_to_time(s_time),
                "end_time": minutes_to_time(e_time)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # If no schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()