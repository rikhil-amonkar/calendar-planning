from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends and their details
    friends = {
        "Steven": {"location": "North Beach", "start": 17.5, "end": 20.5, "min_duration": 0.25},
        "Sarah": {"location": "Golden Gate Park", "start": 17.0, "end": 19.25, "min_duration": 1.25},
        "Brian": {"location": "Embarcadero", "start": 14.25, "end": 16.0, "min_duration": 1.75},
        "Stephanie": {"location": "Haight-Ashbury", "start": 10.25, "end": 12.25, "min_duration": 1.25},
        "Melissa": {"location": "Richmond District", "start": 14.0, "end": 19.5, "min_duration": 0.5},
        "Nancy": {"location": "Nob Hill", "start": 8.25, "end": 12.75, "min_duration": 1.5},
        "David": {"location": "Marina District", "start": 11.25, "end": 13.25, "min_duration": 2.0},
        "James": {"location": "Presidio", "start": 15.0, "end": 18.25, "min_duration": 2.0},
        "Elizabeth": {"location": "Union Square", "start": 11.5, "end": 21.0, "min_duration": 1.0},
        "Robert": {"location": "Financial District", "start": 13.25, "end": 15.25, "min_duration": 0.75}
    }

    # Complete travel times (in hours)
    travel_times = {
        "The Castro": {
            "North Beach": 20/60, "Golden Gate Park": 11/60, "Embarcadero": 22/60,
            "Haight-Ashbury": 6/60, "Richmond District": 16/60, "Nob Hill": 16/60,
            "Marina District": 21/60, "Presidio": 20/60, "Union Square": 19/60,
            "Financial District": 21/60
        },
        "North Beach": {
            "The Castro": 23/60, "Golden Gate Park": 22/60, "Embarcadero": 6/60,
            "Haight-Ashbury": 18/60, "Richmond District": 18/60, "Nob Hill": 7/60,
            "Marina District": 9/60, "Presidio": 17/60, "Union Square": 7/60,
            "Financial District": 8/60
        },
        "Golden Gate Park": {
            "The Castro": 13/60, "North Beach": 23/60, "Embarcadero": 25/60,
            "Haight-Ashbury": 7/60, "Richmond District": 7/60, "Nob Hill": 20/60,
            "Marina District": 16/60, "Presidio": 11/60, "Union Square": 22/60,
            "Financial District": 26/60
        },
        "Embarcadero": {
            "The Castro": 25/60, "North Beach": 5/60, "Golden Gate Park": 25/60,
            "Haight-Ashbury": 21/60, "Richmond District": 21/60, "Nob Hill": 10/60,
            "Marina District": 12/60, "Presidio": 20/60, "Union Square": 10/60,
            "Financial District": 5/60
        },
        "Haight-Ashbury": {
            "The Castro": 6/60, "North Beach": 19/60, "Golden Gate Park": 7/60,
            "Embarcadero": 20/60, "Richmond District": 10/60, "Nob Hill": 15/60,
            "Marina District": 17/60, "Presidio": 15/60, "Union Square": 19/60,
            "Financial District": 21/60
        },
        "Richmond District": {
            "The Castro": 16/60, "North Beach": 17/60, "Golden Gate Park": 9/60,
            "Embarcadero": 19/60, "Haight-Ashbury": 10/60, "Nob Hill": 17/60,
            "Marina District": 9/60, "Presidio": 7/60, "Union Square": 21/60,
            "Financial District": 22/60
        },
        "Nob Hill": {
            "The Castro": 17/60, "North Beach": 8/60, "Golden Gate Park": 17/60,
            "Embarcadero": 9/60, "Haight-Ashbury": 13/60, "Richmond District": 14/60,
            "Marina District": 11/60, "Presidio": 17/60, "Union Square": 7/60,
            "Financial District": 9/60
        },
        "Marina District": {
            "The Castro": 22/60, "North Beach": 11/60, "Golden Gate Park": 18/60,
            "Embarcadero": 14/60, "Haight-Ashbury": 16/60, "Richmond District": 11/60,
            "Nob Hill": 12/60, "Presidio": 10/60, "Union Square": 16/60,
            "Financial District": 17/60
        },
        "Presidio": {
            "The Castro": 21/60, "North Beach": 18/60, "Golden Gate Park": 12/60,
            "Embarcadero": 20/60, "Haight-Ashbury": 15/60, "Richmond District": 7/60,
            "Nob Hill": 18/60, "Marina District": 11/60, "Union Square": 22/60,
            "Financial District": 23/60
        },
        "Union Square": {
            "The Castro": 17/60, "North Beach": 10/60, "Golden Gate Park": 22/60,
            "Embarcadero": 11/60, "Haight-Ashbury": 18/60, "Richmond District": 20/60,
            "Nob Hill": 9/60, "Marina District": 18/60, "Presidio": 24/60,
            "Financial District": 9/60
        },
        "Financial District": {
            "The Castro": 20/60, "North Beach": 7/60, "Golden Gate Park": 23/60,
            "Embarcadero": 4/60, "Haight-Ashbury": 19/60, "Richmond District": 21/60,
            "Nob Hill": 8/60, "Marina District": 15/60, "Presidio": 22/60,
            "Union Square": 9/60
        }
    }

    # Variables for each meeting
    meetings = {}
    meet_vars = {}
    for name in friends:
        meet_vars[name] = Bool(f"meet_{name}")
        meetings[name] = {
            "start": Real(f"{name}_start"),
            "end": Real(f"{name}_end"),
            "duration": Real(f"{name}_duration")
        }
        # If we meet this friend, enforce constraints
        s.add(Implies(meet_vars[name], meetings[name]["duration"] >= friends[name]["min_duration"]))
        s.add(Implies(meet_vars[name], meetings[name]["start"] >= friends[name]["start"]))
        s.add(Implies(meet_vars[name], meetings[name]["end"] <= friends[name]["end"]))
        s.add(Implies(meet_vars[name], meetings[name]["end"] == meetings[name]["start"] + meetings[name]["duration"]))

    # Current location starts at The Castro at 9:00 AM
    current_time = 9.0
    current_location = "The Castro"

    # We need to meet exactly 8 people
    s.add(Sum([If(meet_vars[name], 1, 0) for name in friends]) == 8)

    # Order of meetings is not fixed - we need to find a sequence
    # Create a list of all possible meetings we might attend
    possible_meetings = [name for name in friends]

    # Create variables for the order
    order = [Int(f"order_{i}") for i in range(len(possible_meetings))]
    # Each order variable should be between 0 and len(possible_meetings)-1
    for o in order:
        s.add(o >= 0)
        s.add(o < len(possible_meetings))
    # All order variables should be distinct
    s.add(Distinct(order))

    # Variables to track time and location after each meeting
    times = [Real(f"time_{i}") for i in range(len(possible_meetings)+1)]
    locations = [String(f"loc_{i}") for i in range(len(possible_meetings)+1)]
    s.add(times[0] == current_time)
    s.add(locations[0] == current_location)

    # Constraints for each position in the order
    for i in range(len(possible_meetings)):
        name = possible_meetings[order[i]]
        # If we meet this person
        s.add(Implies(meet_vars[name], 
                      And(times[i+1] == meetings[name]["end"],
                          locations[i+1] == friends[name]["location"],
                          meetings[name]["start"] >= times[i] + travel_times[locations[i]][friends[name]["location"]])))
        # If we don't meet this person
        s.add(Implies(Not(meet_vars[name]),
                      And(times[i+1] == times[i],
                          locations[i+1] == locations[i])))

    # Objective: maximize total meeting time
    total_time = Sum([If(meet_vars[name], meetings[name]["duration"], 0) for name in friends])
    s.maximize(total_time)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        met_count = 0
        schedule = []
        for name in friends:
            if is_true(m[meet_vars[name]]):
                start = m[meetings[name]["start"]].as_fraction()
                end = m[meetings[name]["end"]].as_fraction()
                duration = m[meetings[name]["duration"]].as_fraction()
                print(f"Meet {name} at {friends[name]['location']} from {float(start):.2f} to {float(end):.2f} (duration: {float(duration):.2f} hours)")
                met_count += 1
                schedule.append((float(start), name))
        print(f"\nTotal friends met: {met_count}")
        # Print schedule in chronological order
        print("\nSchedule in order:")
        for time, name in sorted(schedule):
            print(f"{time:.2f}: Meet {name} at {friends[name]['location']}")
    else:
        print("No feasible schedule found to meet exactly 8 friends.")

solve_scheduling()