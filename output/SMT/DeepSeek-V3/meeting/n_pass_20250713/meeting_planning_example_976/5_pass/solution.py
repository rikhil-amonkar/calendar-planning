from z3 import *

def solve_scheduling():
    # Locations and friends' data
    friends = {
        "Matthew": {"location": "Bayview", "start": 19.25, "end": 22.0, "min_duration": 2.0},
        "Karen": {"location": "Chinatown", "start": 19.25, "end": 21.25, "min_duration": 1.5},
        "Sarah": {"location": "Alamo Square", "start": 20.0, "end": 21.75, "min_duration": 1.75},
        "Jessica": {"location": "Nob Hill", "start": 16.5, "end": 18.75, "min_duration": 2.0},
        "Stephanie": {"location": "Presidio", "start": 7.5, "end": 10.25, "min_duration": 1.0},
        "Mary": {"location": "Union Square", "start": 16.75, "end": 21.5, "min_duration": 1.0},
        "Charles": {"location": "The Castro", "start": 16.5, "end": 22.0, "min_duration": 1.75},
        "Nancy": {"location": "North Beach", "start": 14.75, "end": 20.0, "min_duration": 0.25},
        "Thomas": {"location": "Fisherman's Wharf", "start": 13.5, "end": 19.0, "min_duration": 0.5},
        "Brian": {"location": "Marina District", "start": 12.25, "end": 18.0, "min_duration": 1.0},
    }

    # Travel times (in hours)
    travel_times = {
        ("Marina District", "Fisherman's Wharf"): 10/60,
        # Add other necessary travel times here
    }

    # Initialize Z3 optimizer
    opt = Optimize()

    # Variables: start and end times for each friend, and whether they are met
    meet_vars = {}
    start_vars = {}
    end_vars = {}
    for friend in friends:
        meet_vars[friend] = Bool(f"meet_{friend}")
        start_vars[friend] = Real(f"start_{friend}")
        end_vars[friend] = Real(f"end_{friend}")

    # Constraints for each friend
    for friend in friends:
        data = friends[friend]
        # Ensure meeting starts after the friend's availability start time AND after 9:00 AM
        opt.add(Implies(meet_vars[friend], start_vars[friend] >= max(data["start"], 9.0)))
        opt.add(Implies(meet_vars[friend], end_vars[friend] <= data["end"]))
        opt.add(Implies(meet_vars[friend], end_vars[friend] - start_vars[friend] >= data["min_duration"]))

    # Travel time constraints
    # For all pairs of friends that might need travel time between them
    friend_pairs = [("Brian", "Thomas")]  # Add other pairs as needed
    for (friend1, friend2) in friend_pairs:
        loc1 = friends[friend1]["location"]
        loc2 = friends[friend2]["location"]
        if (loc1, loc2) in travel_times:
            travel_time = travel_times[(loc1, loc2)]
            opt.add(Implies(And(meet_vars[friend1], meet_vars[friend2]),
                   Or(
                       start_vars[friend2] >= end_vars[friend1] + travel_time,
                       start_vars[friend1] >= end_vars[friend2] + travel_time
                   )))

    # Constraint: Exactly 6 friends must be met
    opt.add(Sum([If(meet_vars[friend], 1, 0) for friend in friends]) == 6)

    # Solve
    if opt.check() == sat:
        m = opt.model()
        met_friends = []
        for friend in friends:
            if m.evaluate(meet_vars[friend]):
                start = m.evaluate(start_vars[friend])
                end = m.evaluate(end_vars[friend])
                met_friends.append((friend, float(start.as_fraction()), float(end.as_fraction())))
        met_friends.sort(key=lambda x: x[1])  # Sort by start time
        return met_friends
    else:
        return None

solution = solve_scheduling()
if solution:
    print("SOLUTION:")
    for friend, start, end in solution:
        print(f"Meet {friend} from {start:.2f} to {end:.2f}")
else:
    print("No solution found.")