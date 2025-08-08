from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Linda", "location": "Marina District", "start": 18*60, "end": 22*60, "duration": 30},
        {"name": "Kenneth", "location": "The Castro", "start": 14*60 + 45, "end": 16*60 + 15, "duration": 30},
        {"name": "Kimberly", "location": "Richmond District", "start": 14*60 + 15, "end": 22*60, "duration": 30},
        {"name": "Paul", "location": "Alamo Square", "start": 21*60, "end": 21*60 + 30, "duration": 15},
        {"name": "Carol", "location": "Financial District", "start": 10*60 + 15, "end": 12*60, "duration": 60},
        {"name": "Brian", "location": "Presidio", "start": 10*60, "end": 21*60 + 30, "duration": 75},
        {"name": "Laura", "location": "Mission District", "start": 16*60 + 15, "end": 20*60 + 30, "duration": 30},
        {"name": "Sandra", "location": "Nob Hill", "start": 9*60 + 15, "end": 18*60 + 30, "duration": 60},
        {"name": "Karen", "location": "Russian Hill", "start": 18*60 + 30, "end": 22*60, "duration": 75}
    ]

    # Create variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    for friend in friends:
        friend["start_var"] = Int(f"start_{friend['name']}")
        friend["end_var"] = Int(f"end_{friend['name']}")
        s.add(friend["start_var"] >= friend["start"] - 540)  # Convert to minutes since 9:00 AM
        s.add(friend["end_var"] <= friend["end"] - 540)
        s.add(friend["end_var"] - friend["start_var"] >= friend["duration"])

    # Define the order of meetings and travel times
    # We need to ensure that travel time is accounted for between consecutive meetings
    # This is a complex part; for simplicity, we'll assume a fixed order and add constraints accordingly
    # Alternatively, we can use a more sophisticated approach with sequencing variables
    # For this example, we'll define a possible order and add constraints

    # Define travel times between locations (in minutes)
    travel_times = {
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Russian Hill"): 8,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Russian Hill"): 13,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Russian Hill"): 11,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Russian Hill"): 15,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Nob Hill"): 5
    }

    # To simplify, we'll assume a possible order and add constraints
    # This is a heuristic and may not find the optimal solution
    # A better approach would be to use a more sophisticated scheduling algorithm
    # For this example, we'll prioritize friends with tighter time windows

    # Define a possible order: Sandra, Carol, Brian, Kenneth, Laura, Kimberly, Linda, Karen, Paul
    order = ["Sandra", "Carol", "Brian", "Kenneth", "Laura", "Kimberly", "Linda", "Karen", "Paul"]
    for i in range(len(order) - 1):
        current = next(f for f in friends if f["name"] == order[i])
        next_friend = next(f for f in friends if f["name"] == order[i + 1])
        travel_time = travel_times.get((current["location"], next_friend["location"]), 0)
        s.add(next_friend["start_var"] >= current["end_var"] + travel_time)

    # Ensure all meetings are scheduled
    for friend in friends:
        s.add(friend["start_var"] >= 0)
        s.add(friend["end_var"] <= 22*60 - 540)  # 10:00 PM is 22:00

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            start = m.evaluate(friend["start_var"]).as_long() + 540
            end = m.evaluate(friend["end_var"]).as_long() + 540
            start_h = start // 60
            start_m = start % 60
            end_h = end // 60
            end_m = end % 60
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))