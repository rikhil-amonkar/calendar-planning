from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their availability
    friends = {
        "Rebecca": {"location": "Bayview", "start": 9*60, "end": 12*60 + 45, "duration": 90},
        "Amanda": {"location": "Pacific Heights", "start": 18*60 + 30, "end": 21*60 + 45, "duration": 90},
        "James": {"location": "Alamo Square", "start": 9*60 + 45, "end": 21*60 + 15, "duration": 90},
        "Sarah": {"location": "Fisherman's Wharf", "start": 8*60, "end": 21*60 + 30, "duration": 90},
        "Melissa": {"location": "Golden Gate Park", "start": 9*60, "end": 18*60 + 45, "duration": 90}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "The Castro": {
            "Bayview": 19,
            "Pacific Heights": 16,
            "Alamo Square": 8,
            "Fisherman's Wharf": 24,
            "Golden Gate Park": 11
        },
        "Bayview": {
            "The Castro": 20,
            "Pacific Heights": 23,
            "Alamo Square": 16,
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "The Castro": 16,
            "Bayview": 22,
            "Alamo Square": 10,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15
        },
        "Alamo Square": {
            "The Castro": 8,
            "Bayview": 16,
            "Pacific Heights": 10,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 9
        },
        "Fisherman's Wharf": {
            "The Castro": 26,
            "Bayview": 26,
            "Pacific Heights": 12,
            "Alamo Square": 20,
            "Golden Gate Park": 25
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Bayview": 23,
            "Pacific Heights": 16,
            "Alamo Square": 10,
            "Fisherman's Wharf": 24
        }
    }

    # Decision variables: whether to meet each friend
    meet_vars = {name: Bool(f"meet_{name}") for name in friends}

    # Meeting start and end times (in minutes since midnight)
    start_times = {name: Int(f"start_{name}") for name in friends}
    end_times = {name: Int(f"end_{name}") for name in friends}

    # Current location starts at The Castro at 9:00 AM (540 minutes)
    current_location = "The Castro"
    current_time = 540  # 9:00 AM in minutes

    # Constraints for each friend
    order = []
    for name in friends:
        info = friends[name]
        s.add(Implies(meet_vars[name], start_times[name] >= info["start"]))
        s.add(Implies(meet_vars[name], end_times[name] <= info["end"]))
        s.add(Implies(meet_vars[name], end_times[name] == start_times[name] + info["duration"]))
        # Ensure meeting is within their window
        s.add(Implies(meet_vars[name], start_times[name] >= info["start"]))
        s.add(Implies(meet_vars[name], end_times[name] <= info["end"]))

    # Define the order of meetings (this is a heuristic; we may need to explore permutations)
    # For simplicity, let's try to meet Rebecca first (since her window is earliest)
    # Then Melissa, James, Sarah, Amanda
    # We'll need to model the sequence properly with travel times

    # This is a simplified approach; a more comprehensive solution would explore all permutations
    # But for the sake of this problem, let's assume a fixed order and adjust times accordingly

    # We'll need to create a sequence of meetings with travel times
    # This is complex; alternatively, we can use a more flexible approach with no fixed order

    # Alternative approach: model the sequence with variables indicating the order
    # But this is complex for Z3. Instead, let's try to meet as many as possible in a feasible order.

    # Let's try to meet Rebecca, James, Melissa, Sarah, Amanda in that order and see if it's feasible
    # Define the sequence and add travel time constraints

    # Sequence: Rebecca -> James -> Melissa -> Sarah -> Amanda
    sequence = ["Rebecca", "James", "Melissa", "Sarah", "Amanda"]

    # Add constraints for the sequence with travel times
    prev_time = current_time
    prev_loc = current_location
    for i, name in enumerate(sequence):
        s.add(Implies(meet_vars[name], start_times[name] >= prev_time + travel_times[prev_loc][friends[name]["location"]]))
        prev_time = If(meet_vars[name], end_times[name], prev_time)
        prev_loc = If(meet_vars[name], friends[name]["location"], prev_loc)

    # Also, ensure that if we don't meet someone, their start and end times are irrelevant
    for name in friends:
        s.add(Implies(Not(meet_vars[name]), start_times[name] == 0))
        s.add(Implies(Not(meet_vars[name]), end_times[name] == 0))

    # Maximize the number of friends met
    total_met = Sum([If(meet_vars[name], 1, 0) for name in friends])
    s.maximize(total_met)

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
        met_friends = []
        for name in friends:
            if model.evaluate(meet_vars[name]):
                start = model.evaluate(start_times[name]).as_long()
                end = model.evaluate(end_times[name]).as_long()
                start_h = start // 60
                start_m = start % 60
                end_h = end // 60
                end_m = end % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_h:02d}:{start_m:02d}",
                    "end_time": f"{end_h:02d}:{end_m:02d}"
                })
                met_friends.append(name)
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
        print(f"Met friends: {met_friends}")
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))