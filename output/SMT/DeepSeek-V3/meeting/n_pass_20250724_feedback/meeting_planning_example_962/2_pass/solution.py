from z3 import *
import json

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the travel times between locations (in minutes)
    travel_times = {
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Sunset District"): 17,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Sunset District"): 19,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Sunset District"): 15,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Sunset District"): 27,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Sunset District"): 30,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Sunset District"): 11,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Sunset District"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
    }

    # Define the friends and their constraints
    friends = [
        {"name": "Elizabeth", "location": "Marina District", "start": 19*60, "end": 20*60 + 45, "duration": 105},
        {"name": "Joshua", "location": "Presidio", "start": 8*60 + 30, "end": 13*60 + 15, "duration": 105},
        {"name": "Timothy", "location": "North Beach", "start": 19*60 + 45, "end": 22*60, "duration": 90},
        {"name": "David", "location": "Embarcadero", "start": 10*60 + 45, "end": 12*60 + 30, "duration": 30},
        {"name": "Kimberly", "location": "Haight-Ashbury", "start": 16*60 + 45, "end": 21*60 + 30, "duration": 75},
        {"name": "Lisa", "location": "Golden Gate Park", "start": 17*60 + 30, "end": 21*60 + 45, "duration": 45},
        {"name": "Ronald", "location": "Richmond District", "start": 8*60, "end": 9*60 + 30, "duration": 90},
        {"name": "Stephanie", "location": "Alamo Square", "start": 15*60 + 30, "end": 16*60 + 30, "duration": 30},
        {"name": "Helen", "location": "Financial District", "start": 17*60 + 30, "end": 18*60 + 30, "duration": 45},
        {"name": "Laura", "location": "Sunset District", "start": 17*60 + 45, "end": 21*60 + 15, "duration": 90},
    ]

    # Create variables for each friend's meeting start and end times
    for friend in friends:
        friend["start_var"] = Int(f"{friend['name']}_start")
        friend["end_var"] = Int(f"{friend['name']}_end")
        s.add(friend["start_var"] >= friend["start"])
        s.add(friend["end_var"] <= friend["end"])
        s.add(friend["end_var"] - friend["start_var"] >= friend["duration"])

    # Add constraints for travel times between consecutive meetings
    # We'll try to meet friends in order of their earliest possible start times
    ordered_friends = sorted(friends, key=lambda x: x["start"])

    current_location = "The Castro"
    current_time = 9 * 60  # Start at 9:00 AM

    for friend in ordered_friends:
        travel_time = travel_times.get((current_location, friend["location"]), 0)
        s.add(friend["start_var"] >= current_time + travel_time)
        current_location = friend["location"]
        current_time = friend["end_var"]

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        result = []
        for friend in friends:
            start = model[friend["start_var"]].as_long()
            end = model[friend["end_var"]].as_long()
            result.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": f"{start // 60:02d}:{start % 60:02d}",
                "end_time": f"{end // 60:02d}:{end % 60:02d}",
            })
        # Sort the itinerary by start time
        result.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:]))
        return {"itinerary": result}
    else:
        return {"itinerary": []}

# Run the solver and print the result
solution = solve_scheduling()
print(json.dumps(solution, indent=2))