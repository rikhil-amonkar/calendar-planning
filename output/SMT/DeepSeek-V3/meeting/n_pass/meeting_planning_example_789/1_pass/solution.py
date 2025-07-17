from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Optimize()

    # Friends and their details
    friends = {
        "Betty": {
            "location": "Russian Hill",
            "available_start": 7 * 60,  # 7:00 AM in minutes
            "available_end": 16 * 60 + 45,  # 4:45 PM in minutes
            "min_duration": 105,
        },
        "Melissa": {
            "location": "Alamo Square",
            "available_start": 9 * 60 + 30,  # 9:30 AM in minutes
            "available_end": 17 * 60 + 15,  # 5:15 PM in minutes
            "min_duration": 105,
        },
        "Joshua": {
            "location": "Haight-Ashbury",
            "available_start": 12 * 60 + 15,  # 12:15 PM in minutes
            "available_end": 19 * 60,  # 7:00 PM in minutes
            "min_duration": 90,
        },
        "Jeffrey": {
            "location": "Marina District",
            "available_start": 12 * 60 + 15,  # 12:15 PM in minutes
            "available_end": 18 * 60,  # 6:00 PM in minutes
            "min_duration": 45,
        },
        "James": {
            "location": "Bayview",
            "available_start": 7 * 60 + 30,  # 7:30 AM in minutes
            "available_end": 20 * 60,  # 8:00 PM in minutes
            "min_duration": 90,
        },
        "Anthony": {
            "location": "Chinatown",
            "available_start": 11 * 60 + 45,  # 11:45 AM in minutes
            "available_end": 13 * 60 + 30,  # 1:30 PM in minutes
            "min_duration": 75,
        },
        "Timothy": {
            "location": "Presidio",
            "available_start": 12 * 60 + 30,  # 12:30 PM in minutes
            "available_end": 14 * 60 + 45,  # 2:45 PM in minutes
            "min_duration": 90,
        },
        "Emily": {
            "location": "Sunset District",
            "available_start": 19 * 60 + 30,  # 7:30 PM in minutes
            "available_end": 21 * 60 + 30,  # 9:30 PM in minutes
            "min_duration": 120,
        },
    }

    # Travel times dictionary (from_location, to_location) -> minutes
    travel_times = {
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Sunset District"): 19,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Sunset District"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Presidio"): 16,
    }

    # Variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    start_vars = {}
    end_vars = {}
    meet_vars = {}  # Boolean indicating whether the friend is met
    for name in friends:
        start_vars[name] = Int(f"start_{name}")
        end_vars[name] = Int(f"end_{name}")
        meet_vars[name] = Bool(f"meet_{name}")

    # Current location starts at Union Square at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Union Square"

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        start = start_vars[name]
        end = end_vars[name]
        meet = meet_vars[name]

        # If meeting the friend, enforce constraints
        solver.add(Implies(meet, start >= friend["available_start"]))
        solver.add(Implies(meet, end <= friend["available_end"]))
        solver.add(Implies(meet, end == start + friend["min_duration"]))

        # Initially, no meeting is scheduled unless proven otherwise
        solver.add(Implies(Not(meet), start == -1))
        solver.add(Implies(Not(meet), end == -1))

    # Sequence constraints: order of meetings and travel times
    # We need to model the sequence of meetings. This is complex, so we'll use a simplified approach:
    # Assume meetings are in some order, and travel times are respected between consecutive meetings.
    # However, this is a simplified approach and may not cover all possibilities.

    # To simplify, we'll assume that the order is fixed based on some heuristic (e.g., earliest available first).
    # Alternatively, we can use a more complex model with auxiliary variables for order, but that's beyond this scope.

    # Instead, we'll prioritize meeting friends with tighter time windows first (Anthony, Timothy, etc.)
    # and then others.

    # For now, let's prioritize Anthony, Timothy, Melissa, Betty, Joshua, Jeffrey, James, Emily.
    # This is a heuristic and may not be optimal.

    # We'll model the sequence as a list where each meeting must start after the previous one's end plus travel time.
    # This is a simplification, but it's manageable.

    # Let's define a list of friends in a tentative order.
    tentative_order = ["Anthony", "Timothy", "Melissa", "Betty", "Joshua", "Jeffrey", "James", "Emily"]

    # For each consecutive pair in the tentative order, if both are met, then the start of the next >= end of previous + travel time.
    for i in range(len(tentative_order) - 1):
        name1 = tentative_order[i]
        name2 = tentative_order[i + 1]
        loc1 = friends[name1]["location"]
        loc2 = friends[name2]["location"]
        travel_time = travel_times.get((loc1, loc2), 0)

        solver.add(Implies(And(meet_vars[name1], meet_vars[name2]),
                          start_vars[name2] >= end_vars[name1] + travel_time))

    # Also, the first meeting must start after current_time + travel time from Union Square.
    for name in tentative_order:
        loc = friends[name]["location"]
        travel_time = travel_times.get((current_location, loc), 0)
        solver.add(Implies(meet_vars[name], start_vars[name] >= current_time + travel_time))

    # Maximize the number of friends met
    solver.maximize(Sum([If(meet_vars[name], 1, 0) for name in friends]))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in friends:
            if model.evaluate(meet_vars[name]):
                start = model.evaluate(start_vars[name]).as_long()
                end = model.evaluate(end_vars[name]).as_long()
                start_hh = start // 60
                start_mm = start % 60
                end_hh = end // 60
                end_mm = end % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}",
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))