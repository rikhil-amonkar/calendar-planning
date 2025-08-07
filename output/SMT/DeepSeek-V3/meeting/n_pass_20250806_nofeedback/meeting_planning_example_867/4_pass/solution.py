from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times as a dictionary for easy lookup
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Sunset District'): 27,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Bayview'): 27,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 25,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Fisherman\'s Wharf'): 29,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Sunset District'): 10,
    }

    # Define friends and their constraints
    friends = [
        {"name": "Elizabeth", "location": "Mission District", "start": 10.5, "end": 20.0, "duration": 1.5},
        {"name": "David", "location": "Union Square", "start": 15.25, "end": 19.0, "duration": 0.75},
        {"name": "Sandra", "location": "Pacific Heights", "start": 7.0, "end": 20.0, "duration": 2.0},
        {"name": "Thomas", "location": "Bayview", "start": 19.5, "end": 20.5, "duration": 0.5},
        {"name": "Robert", "location": "Fisherman's Wharf", "start": 10.0, "end": 15.0, "duration": 0.25},
        {"name": "Kenneth", "location": "Marina District", "start": 10.75, "end": 13.0, "duration": 0.75},
        {"name": "Melissa", "location": "Richmond District", "start": 18.25, "end": 20.0, "duration": 0.25},
        {"name": "Kimberly", "location": "Sunset District", "start": 10.25, "end": 18.25, "duration": 1.75},
        {"name": "Amanda", "location": "Golden Gate Park", "start": 7.75, "end": 18.75, "duration": 0.25}
    ]

    # Create variables for each meeting's start and end times
    for friend in friends:
        friend["start_var"] = Real(f"{friend['name']}_start")
        friend["end_var"] = Real(f"{friend['name']}_end")
        s.add(friend["start_var"] >= friend["start"])
        s.add(friend["end_var"] <= friend["end"])
        s.add(friend["end_var"] - friend["start_var"] >= friend["duration"])

    # Initial location is Haight-Ashbury at 9:00 AM
    current_location = "Haight-Ashbury"
    current_time = 9.0

    # Define the order of meetings (this is a simplification; in practice, we'd need to model all possible orders)
    # For simplicity, we'll assume an order that tries to meet all friends
    # This is a heuristic and may not find the optimal solution; a more complete approach would involve permutations
    meeting_order = ["Amanda", "Robert", "Kenneth", "Kimberly", "Elizabeth", "David", "Melissa", "Thomas", "Sandra"]

    # Add constraints for travel times between meetings
    prev_person = None
    for person in meeting_order:
        friend = next(f for f in friends if f["name"] == person)
        if prev_person is not None:
            prev_friend = next(f for f in friends if f["name"] == prev_person)
            travel_time = travel_times.get((prev_friend["location"], friend["location"]), 0) / 60.0
            s.add(friend["start_var"] >= prev_friend["end_var"] + travel_time)
        else:
            travel_time = travel_times.get((current_location, friend["location"]), 0) / 60.0
            s.add(friend["start_var"] >= current_time + travel_time)
        prev_person = person

    # Check if the solution is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            start = m[friend["start_var"]].as_fraction()
            end = m[friend["end_var"]].as_fraction()
            start_time = float(start.numerator) / float(start.denominator)
            end_time = float(end.numerator) / float(end.denominator)
            # Convert to HH:MM format
            start_h = int(start_time)
            start_m = int((start_time - start_h) * 60)
            end_h = int(end_time)
            end_m = int((end_time - end_h) * 60)
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))