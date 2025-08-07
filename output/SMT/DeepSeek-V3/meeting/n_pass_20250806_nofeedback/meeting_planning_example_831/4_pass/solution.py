from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Friends and their details
    friends = {
        "Jeffrey": {"location": "Fisherman's Wharf", "start": 615, "end": 780, "min_duration": 90},
        "Ronald": {"location": "Alamo Square", "start": 465, "end": 885, "min_duration": 120},
        "Jason": {"location": "Financial District", "start": 645, "end": 960, "min_duration": 105},
        "Melissa": {"location": "Union Square", "start": 1065, "end": 1095, "min_duration": 15},
        "Elizabeth": {"location": "Sunset District", "start": 885, "end": 1050, "min_duration": 105},
        "Margaret": {"location": "Embarcadero", "start": 795, "end": 1140, "min_duration": 90},
        "George": {"location": "Golden Gate Park", "start": 1140, "end": 1260, "min_duration": 75},
        "Richard": {"location": "Chinatown", "start": 570, "end": 1260, "min_duration": 15},
        "Laura": {"location": "Richmond District", "start": 585, "end": 1080, "min_duration": 60}
    }

    # Travel times (in minutes)
    travel_times = {
        "Presidio": {
            "Fisherman's Wharf": 19, "Alamo Square": 19, "Financial District": 23,
            "Union Square": 22, "Sunset District": 15, "Embarcadero": 20,
            "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
        },
        "Fisherman's Wharf": {
            "Presidio": 17, "Alamo Square": 21, "Financial District": 11,
            "Union Square": 13, "Sunset District": 27, "Embarcadero": 8,
            "Golden Gate Park": 25, "Chinatown": 12, "Richmond District": 18
        },
        # ... (other locations' travel times remain the same)
    }

    # Variables for meeting start times
    start_times = {name: Int(f"start_{name}") for name in friends}
    # Variables indicating if meeting is scheduled
    scheduled = {name: Bool(f"scheduled_{name}") for name in friends}

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Presidio"

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(Implies(scheduled[name], 
                     And(start_times[name] >= friend["start"],
                         start_times[name] + friend["min_duration"] <= friend["end"])))

    # Ensure we don't schedule overlapping meetings with travel time
    # We'll use a sequence variable to determine order
    sequence = [Int(f"seq_{i}") for i in range(len(friends))]
    s.add(Distinct(sequence))
    for i in range(len(friends)):
        s.add(sequence[i] >= 0)
        s.add(sequence[i] < len(friends))

    # Link sequence to actual meetings
    prev_end = current_time
    prev_loc = current_location
    for i in range(len(friends)):
        # Get which friend is at position i
        for j, name in enumerate(friends):
            friend = friends[name]
            # If this friend is at position i in sequence
            s.add(Implies(sequence[i] == j,
                         And(scheduled[name],
                             start_times[name] >= prev_end + travel_times[prev_loc][friend["location"]],
                             prev_end == start_times[name] + friend["min_duration"],
                             prev_loc == friend["location"])))

    # Maximize number of friends met
    s.maximize(Sum([If(scheduled[name], 1, 0) for name in friends]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Get the meeting order from the sequence
        seq_order = sorted([(model.evaluate(sequence[i]).as_long(), i) 
                          for i in range(len(friends))], key=lambda x: x[0])
        
        for pos, i in seq_order:
            name = list(friends.keys())[i]
            if model.evaluate(scheduled[name]):
                start = model.evaluate(start_times[name]).as_long()
                end = start + friends[name]["min_duration"]
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}"
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))