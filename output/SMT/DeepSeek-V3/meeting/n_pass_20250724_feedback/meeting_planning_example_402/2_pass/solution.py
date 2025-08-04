from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Define the friends and their availability
    friends = {
        "Sarah": {"location": "Haight-Ashbury", "start": 17*60, "end": 21*60 + 30, "duration": 105},
        "Patricia": {"location": "Sunset District", "start": 17*60, "end": 19*60 + 45, "duration": 45},
        "Matthew": {"location": "Marina District", "start": 9*60 + 15, "end": 12*60, "duration": 15},
        "Joseph": {"location": "Financial District", "start": 14*60 + 15, "end": 18*60 + 45, "duration": 30},
        "Robert": {"location": "Union Square", "start": 10*60 + 15, "end": 21*60 + 45, "duration": 15}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Sunset District": 10,
            "Marina District": 16,
            "Financial District": 26,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Golden Gate Park": 7,
            "Sunset District": 15,
            "Marina District": 17,
            "Financial District": 21,
            "Union Square": 17
        },
        "Sunset District": {
            "Golden Gate Park": 11,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Financial District": 30,
            "Union Square": 30
        },
        "Marina District": {
            "Golden Gate Park": 18,
            "Haight-Ashbury": 16,
            "Sunset District": 19,
            "Financial District": 17,
            "Union Square": 16
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Sunset District": 31,
            "Marina District": 15,
            "Union Square": 9
        },
        "Union Square": {
            "Golden Gate Park": 22,
            "Haight-Ashbury": 18,
            "Sunset District": 26,
            "Marina District": 18,
            "Financial District": 9
        }
    }

    # Try all possible permutations of meeting orders
    for order in permutations(friends.keys()):
        s = Solver()

        # Variables for each meeting: start and end times
        meeting_vars = {}
        for name in order:
            meeting_vars[name] = {
                "start": Int(f"start_{name}"),
                "end": Int(f"end_{name}")
            }

        # Current location starts at Golden Gate Park at 9:00AM (540 minutes)
        current_time = 9 * 60
        current_location = "Golden Gate Park"

        # Constraints for each meeting in the current order
        for name in order:
            friend = friends[name]
            start = meeting_vars[name]["start"]
            end = meeting_vars[name]["end"]
            duration = friend["duration"]

            # Meeting must start and end within friend's availability
            s.add(start >= friend["start"])
            s.add(end <= friend["end"])
            s.add(end == start + duration)

            # Travel time from current location to friend's location
            travel_time = travel_times[current_location][friend["location"]]
            s.add(start >= current_time + travel_time)

            # Update current time and location after meeting
            current_time = end
            current_location = friend["location"]

        # Check if the solver can find a solution
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for name in order:
                start_val = model[meeting_vars[name]["start"]].as_long()
                end_val = model[meeting_vars[name]["end"]].as_long()
                start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
                end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
            return {"itinerary": itinerary}

    # If no solution found
    return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))