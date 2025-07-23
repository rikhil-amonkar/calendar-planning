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

    # Create location enumeration
    locations = list(travel_times.keys())
    LocSort, loc_consts = EnumSort('Location', locations)
    loc_map = {loc: loc_consts[i] for i, loc in enumerate(locations)}

    # Variables for each meeting
    meet_vars = {name: Bool(f"meet_{name}") for name in friends}
    start_vars = {name: Real(f"start_{name}") for name in friends}
    end_vars = {name: Real(f"end_{name}") for name in friends}
    duration_vars = {name: Real(f"duration_{name}") for name in friends}

    # Meeting constraints
    for name in friends:
        s.add(Implies(meet_vars[name], duration_vars[name] >= friends[name]["min_duration"]))
        s.add(Implies(meet_vars[name], start_vars[name] >= friends[name]["start"]))
        s.add(Implies(meet_vars[name], end_vars[name] <= friends[name]["end"]))
        s.add(Implies(meet_vars[name], end_vars[name] == start_vars[name] + duration_vars[name]))

    # Must meet exactly 8 people
    s.add(Sum([If(meet_vars[name], 1, 0) for name in friends]) == 8)

    # Current location starts at The Castro at 9:00 AM
    current_time = 9.0
    current_loc = loc_map["The Castro"]

    # Create a list of all possible meetings we might attend
    possible_meetings = list(friends.keys())

    # Create variables for the order - we'll use a different approach
    # We'll create a sequence of meetings with optional gaps
    max_meetings = len(possible_meetings)
    meeting_sequence = [Int(f"seq_{i}") for i in range(max_meetings)]
    
    # Each sequence variable should represent a meeting index (-1 means no meeting)
    for m in meeting_sequence:
        s.add(m >= -1)
        s.add(m < max_meetings)
    
    # Variables to track time and location after each meeting
    times = [Real(f"time_{i}") for i in range(max_meetings+1)]
    locs = [Const(f"loc_{i}", LocSort) for i in range(max_meetings+1)]
    s.add(times[0] == current_time)
    s.add(locs[0] == current_loc)

    # For each position in the sequence
    for i in range(max_meetings):
        # For each possible meeting
        for j, name in enumerate(possible_meetings):
            # If this meeting is at position i
            is_at_pos = (meeting_sequence[i] == j)
            # If we're meeting this person
            s.add(Implies(And(is_at_pos, meet_vars[name]),
                          And(times[i+1] == end_vars[name],
                              locs[i+1] == loc_map[friends[name]["location"]],
                              start_vars[name] >= times[i] + travel_times[locations[locs[i].as_long()]][friends[name]["location"]])))
            # If we're not meeting this person (but it's in our sequence), just carry forward
            s.add(Implies(And(is_at_pos, Not(meet_vars[name])),
                          And(times[i+1] == times[i],
                              locs[i+1] == locs[i])))
        # Handle the case where no meeting is scheduled at this position
        s.add(Implies(meeting_sequence[i] == -1,
                      And(times[i+1] == times[i],
                          locs[i+1] == locs[i])))

    # Objective: maximize total meeting time
    total_time = Sum([If(meet_vars[name], duration_vars[name], 0) for name in friends])
    s.maximize(total_time)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        met_count = 0
        schedule = []
        for name in friends:
            if is_true(m[meet_vars[name]]):
                start = m[start_vars[name]].as_fraction()
                end = m[end_vars[name]].as_fraction()
                duration = m[duration_vars[name]].as_fraction()
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