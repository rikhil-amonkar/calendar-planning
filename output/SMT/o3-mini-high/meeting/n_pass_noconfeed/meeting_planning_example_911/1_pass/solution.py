import json
from z3 import *

def format_time(minutes):
    # Convert integer minutes (since midnight) to "H:MM" 24-hour format
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs}:{mins:02d}"

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Financial District"): 21,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Financial District"): 8,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Financial District"): 26,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Financial District"): 22,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Financial District"): 9,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Financial District"): 17,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Financial District"): 23,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Financial District"): 9,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Union Square"): 9,
    }

    # Define friend meeting data with availability windows and required meeting duration.
    # Times are represented in minutes from midnight.
    # 9:00 AM = 540
    friends = [
        {"name": "Steven", "location": "North Beach", "avail_start": 1050, "avail_end": 1230, "duration": 15},
        {"name": "Sarah", "location": "Golden Gate Park", "avail_start": 1020, "avail_end": 1155, "duration": 75},
        {"name": "Brian", "location": "Embarcadero", "avail_start": 855,  "avail_end": 960,  "duration": 105},
        {"name": "Stephanie", "location": "Haight-Ashbury", "avail_start": 615, "avail_end": 735, "duration": 75},
        {"name": "Melissa", "location": "Richmond District", "avail_start": 840, "avail_end": 1170, "duration": 30},
        {"name": "Nancy", "location": "Nob Hill", "avail_start": 495, "avail_end": 765, "duration": 90},
        {"name": "David", "location": "Marina District", "avail_start": 675, "avail_end": 795, "duration": 120},
        {"name": "James", "location": "Presidio", "avail_start": 900, "avail_end": 1095, "duration": 120},
        {"name": "Elizabeth", "location": "Union Square", "avail_start": 690, "avail_end": 1260, "duration": 60},
        {"name": "Robert", "location": "Financial District", "avail_start": 795, "avail_end": 915, "duration": 45},
    ]

    n = len(friends)
    opt = Optimize()

    # Decision variables for each friend meeting:
    # scheduled[i] indicates if we schedule a meeting with friend i.
    # start_vars[i] and end_vars[i] represent the meeting start and end times.
    # order_vars[i] represents the order position in the daily schedule (0 if not scheduled).
    scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]

    # Add constraints for each meeting based on availability and meeting duration.
    for i, f in enumerate(friends):
        # If scheduled, enforce meeting time within availability, meeting duration, and a valid order.
        opt.add(
            Or(
                Not(scheduled[i]),
                And(
                    start_vars[i] >= f["avail_start"],
                    end_vars[i] <= f["avail_end"],
                    end_vars[i] - start_vars[i] >= f["duration"],
                    start_vars[i] < end_vars[i],
                    order_vars[i] >= 1,
                    order_vars[i] <= n,
                ),
            )
        )
        # If not scheduled, force order to 0.
        opt.add(Or(scheduled[i], order_vars[i] == 0))

    # Enforce that scheduled meetings have distinct order values.
    for i in range(n):
        for j in range(i + 1, n):
            opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))

    # Constraint for the first scheduled meeting:
    # If a meeting is the first in the order then we must account for travel time from "The Castro" (arrival at 9:00 = 540)
    for i, f in enumerate(friends):
        tt = travel_times.get(("The Castro", f["location"]), 0)
        opt.add(Implies(And(scheduled[i], order_vars[i] == 1), start_vars[i] >= 540 + tt))

    # Constraint for consecutive meetings:
    # If friend j is scheduled immediately after friend i (order_j == order_i + 1),
    # then the meeting j must start after friend i's meeting ends plus the travel time from i's location to j's location.
    for i in range(n):
        for j in range(n):
            if i != j:
                tt = travel_times.get((friends[i]["location"], friends[j]["location"]), 0)
                opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[j] == order_vars[i] + 1),
                                 end_vars[i] + tt <= start_vars[j]))

    # Objective: maximize the total number of scheduled meetings.
    total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        # Extract scheduled meetings with their order, start, and end times.
        for i in range(n):
            if is_true(model.evaluate(scheduled[i])):
                order_val = model.evaluate(order_vars[i]).as_long()
                start_val = model.evaluate(start_vars[i]).as_long()
                end_val = model.evaluate(end_vars[i]).as_long()
                scheduled_meetings.append((order_val, {
                    "action": "meet",
                    "location": friends[i]["location"],
                    "person": friends[i]["name"],
                    "start_time": format_time(start_val),
                    "end_time": format_time(end_val)
                }))
        # Sort meetings by their order in the day.
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in scheduled_meetings]
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()