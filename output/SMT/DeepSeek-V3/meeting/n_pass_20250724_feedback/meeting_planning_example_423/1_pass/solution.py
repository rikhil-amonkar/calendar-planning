from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        "Jason": {
            "location": "Richmond District",
            "available_start": 13 * 60,  # 1:00 PM in minutes
            "available_end": 20 * 60 + 45,  # 8:45 PM in minutes
            "min_duration": 90,
        },
        "Melissa": {
            "location": "North Beach",
            "available_start": 18 * 60 + 45,  # 6:45 PM in minutes
            "available_end": 20 * 60 + 15,  # 8:15 PM in minutes
            "min_duration": 45,
        },
        "Brian": {
            "location": "Financial District",
            "available_start": 9 * 60 + 45,  # 9:45 AM in minutes
            "available_end": 21 * 60 + 45,  # 9:45 PM in minutes
            "min_duration": 15,
        },
        "Elizabeth": {
            "location": "Golden Gate Park",
            "available_start": 8 * 60 + 45,  # 8:45 AM in minutes
            "available_end": 21 * 60 + 30,  # 9:30 PM in minutes
            "min_duration": 105,
        },
        "Laura": {
            "location": "Union Square",
            "available_start": 14 * 60 + 15,  # 2:15 PM in minutes
            "available_end": 19 * 60 + 30,  # 7:30 PM in minutes
            "min_duration": 75,
        }
    }

    # Travel times (in minutes) from location A to location B
    travel_times = {
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Union Square"): 22,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Union Square"): 21,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Union Square"): 7,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Union Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22,
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = {"start": start, "end": end}

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = "Presidio"

    # To keep track of the order of meetings
    meeting_order = []
    for name in friends:
        meeting_order.append((name, meeting_vars[name]["start"], meeting_vars[name]["end"]))

    # Constraints for each friend's meeting
    for name in friends:
        info = friends[name]
        start_var = meeting_vars[name]["start"]
        end_var = meeting_vars[name]["end"]

        # Meeting must start and end within the friend's availability
        s.add(start_var >= info["available_start"])
        s.add(end_var <= info["available_end"])
        # Meeting duration must be at least the minimum required
        s.add(end_var - start_var >= info["min_duration"])

    # Ensure no overlapping meetings and account for travel time
    # We need to sequence the meetings properly
    # This is a simplified approach; a more sophisticated one would sequence them optimally
    # For simplicity, we'll assume we can meet all friends by sequencing them properly
    # and adding travel time constraints between consecutive meetings

    # To maximize the number of friends met, we'll try to meet all friends
    # and let Z3 find a feasible schedule

    # We'll sequence the meetings in some order and add travel time constraints
    # For simplicity, let's try to meet Elizabeth first (since she's available earliest)
    # Then Brian, then Laura, then Jason, then Melissa

    # Define the order: Elizabeth, Brian, Laura, Jason, Melissa
    order = ["Elizabeth", "Brian", "Laura", "Jason", "Melissa"]

    # But Melissa's name is "Melissa" in the friends dict, so correcting:
    order = ["Elizabeth", "Brian", "Laura", "Jason", "Melissa"]

    # Add travel time constraints between consecutive meetings
    prev_end = current_time
    prev_location = current_location
    for name in order:
        if name not in friends:
            continue  # Skip if not in friends (e.g., typo)
        start_var = meeting_vars[name]["start"]
        end_var = meeting_vars[name]["end"]
        # Travel time from prev_location to current friend's location
        travel_key = (prev_location, friends[name]["location"])
        travel_time = travel_times.get(travel_key, 0)
        s.add(start_var >= prev_end + travel_time)
        prev_end = end_var
        prev_location = friends[name]["location"]

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
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
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))