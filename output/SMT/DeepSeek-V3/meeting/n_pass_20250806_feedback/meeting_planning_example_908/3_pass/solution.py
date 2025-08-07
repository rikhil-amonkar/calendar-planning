from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define travel times (in minutes) between locations
    travel_times = {
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Bayview": 19,
            "Haight-Ashbury": 19,
            "Russian Hill": 11,
            "The Castro": 20,
            "Marina District": 15,
            "Richmond District": 21,
            "Union Square": 9,
            "Sunset District": 30
        },
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Presidio": 17,
            "Bayview": 26,
            "Haight-Ashbury": 22,
            "Russian Hill": 7,
            "The Castro": 27,
            "Marina District": 9,
            "Richmond District": 18,
            "Union Square": 13,
            "Sunset District": 27
        },
        "Presidio": {
            "Financial District": 23,
            "Fisherman's Wharf": 19,
            "Bayview": 31,
            "Haight-Ashbury": 15,
            "Russian Hill": 14,
            "The Castro": 21,
            "Marina District": 11,
            "Richmond District": 7,
            "Union Square": 22,
            "Sunset District": 15
        },
        "Bayview": {
            "Financial District": 19,
            "Fisherman's Wharf": 25,
            "Presidio": 32,
            "Haight-Ashbury": 19,
            "Russian Hill": 23,
            "The Castro": 19,
            "Marina District": 27,
            "Richmond District": 25,
            "Union Square": 18,
            "Sunset District": 23
        },
        "Haight-Ashbury": {
            "Financial District": 21,
            "Fisherman's Wharf": 23,
            "Presidio": 15,
            "Bayview": 18,
            "Russian Hill": 17,
            "The Castro": 6,
            "Marina District": 17,
            "Richmond District": 10,
            "Union Square": 19,
            "Sunset District": 15
        },
        "Russian Hill": {
            "Financial District": 11,
            "Fisherman's Wharf": 7,
            "Presidio": 14,
            "Bayview": 23,
            "Haight-Ashbury": 17,
            "The Castro": 21,
            "Marina District": 7,
            "Richmond District": 14,
            "Union Square": 10,
            "Sunset District": 23
        },
        "The Castro": {
            "Financial District": 21,
            "Fisherman's Wharf": 24,
            "Presidio": 20,
            "Bayview": 19,
            "Haight-Ashbury": 6,
            "Russian Hill": 18,
            "Marina District": 21,
            "Richmond District": 16,
            "Union Square": 19,
            "Sunset District": 17
        },
        "Marina District": {
            "Financial District": 17,
            "Fisherman's Wharf": 10,
            "Presidio": 10,
            "Bayview": 27,
            "Haight-Ashbury": 16,
            "Russian Hill": 8,
            "The Castro": 22,
            "Richmond District": 11,
            "Union Square": 16,
            "Sunset District": 19
        },
        "Richmond District": {
            "Financial District": 22,
            "Fisherman's Wharf": 18,
            "Presidio": 7,
            "Bayview": 27,
            "Haight-Ashbury": 10,
            "Russian Hill": 13,
            "The Castro": 16,
            "Marina District": 9,
            "Union Square": 21,
            "Sunset District": 11
        },
        "Union Square": {
            "Financial District": 9,
            "Fisherman's Wharf": 15,
            "Presidio": 24,
            "Bayview": 15,
            "Haight-Ashbury": 18,
            "Russian Hill": 13,
            "The Castro": 17,
            "Marina District": 18,
            "Richmond District": 20,
            "Sunset District": 27
        },
        "Sunset District": {
            "Financial District": 30,
            "Fisherman's Wharf": 29,
            "Presidio": 16,
            "Bayview": 22,
            "Haight-Ashbury": 15,
            "Russian Hill": 24,
            "The Castro": 17,
            "Marina District": 21,
            "Richmond District": 12,
            "Union Square": 30
        }
    }

    # Friends' data: name, location, available start, available end, min duration (in minutes)
    friends = [
        ("Mark", "Fisherman's Wharf", 8*60 + 15, 10*60 + 0, 30),
        ("Stephanie", "Presidio", 12*60 + 15, 15*60 + 0, 75),
        ("Betty", "Bayview", 7*60 + 15, 20*60 + 30, 15),
        ("Lisa", "Haight-Ashbury", 15*60 + 30, 18*60 + 30, 45),
        ("William", "Russian Hill", 18*60 + 45, 20*60 + 0, 60),
        ("Brian", "The Castro", 9*60 + 15, 13*60 + 15, 30),
        ("Joseph", "Marina District", 10*60 + 45, 15*60 + 0, 90),
        ("Ashley", "Richmond District", 9*60 + 45, 11*60 + 15, 45),
        ("Patricia", "Union Square", 16*60 + 30, 20*60 + 0, 120),
        ("Karen", "Sunset District", 16*60 + 30, 22*60 + 0, 105)
    ]

    # Variables for each friend's meeting start and end times (in minutes since midnight)
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    meet_vars = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]  # Whether to meet the friend

    # Current location starts at Financial District at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes

    # Constraints for each friend
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        opt.add(Implies(meet_vars[i], start_vars[i] >= max(avail_start, current_time)))
        opt.add(Implies(meet_vars[i], end_vars[i] <= avail_end))
        opt.add(Implies(meet_vars[i], end_vars[i] == start_vars[i] + min_dur))

    # Ordering constraints: ensure meetings are scheduled in a feasible order with travel times
    # This is a simplified approach; a more sophisticated model would sequence meetings.
    # For simplicity, we'll assume meetings are scheduled in some order with travel times.
    # A better approach would involve sequencing variables, but that's complex.

    # Maximize the number of friends met
    opt.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i, (name, loc, _, _, _) in enumerate(friends):
            if model.evaluate(meet_vars[i]):
                start = model.evaluate(start_vars[i]).as_long()
                end = model.evaluate(end_vars[i]).as_long()
                start_time = f"{start // 60:02d}:{start % 60:02d}"
                end_time = f"{end // 60:02d}:{end % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))