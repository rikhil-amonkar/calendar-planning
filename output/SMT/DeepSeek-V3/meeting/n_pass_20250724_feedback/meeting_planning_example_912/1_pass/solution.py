from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their travel times
    locations = [
        "Union Square", "Presidio", "Alamo Square", "Marina District", 
        "Financial District", "Nob Hill", "Sunset District", "Chinatown", 
        "Russian Hill", "North Beach", "Haight-Ashbury"
    ]

    # Travel times dictionary (simplified for Z3)
    travel_times = {
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19,
    }

    # Define the friends and their constraints
    friends = [
        {"name": "Kimberly", "location": "Presidio", "start": (15, 30), "end": (16, 0), "duration": 15},
        {"name": "Elizabeth", "location": "Alamo Square", "start": (19, 15), "end": (20, 15), "duration": 15},
        {"name": "Joshua", "location": "Marina District", "start": (10, 30), "end": (14, 15), "duration": 45},
        {"name": "Sandra", "location": "Financial District", "start": (19, 30), "end": (20, 15), "duration": 45},
        {"name": "Kenneth", "location": "Nob Hill", "start": (12, 45), "end": (21, 45), "duration": 30},
        {"name": "Betty", "location": "Sunset District", "start": (14, 0), "end": (19, 0), "duration": 60},
        {"name": "Deborah", "location": "Chinatown", "start": (17, 15), "end": (20, 30), "duration": 15},
        {"name": "Barbara", "location": "Russian Hill", "start": (17, 30), "end": (21, 15), "duration": 120},
        {"name": "Steven", "location": "North Beach", "start": (17, 45), "end": (20, 45), "duration": 90},
        {"name": "Daniel", "location": "Haight-Ashbury", "start": (18, 30), "end": (18, 45), "duration": 15},
    ]

    # Convert friend times to minutes since 9:00 AM (540 minutes)
    for friend in friends:
        friend["start_min"] = friend["start"][0] * 60 + friend["start"][1] - 540
        friend["end_min"] = friend["end"][0] * 60 + friend["end"][1] - 540

    # Create Z3 variables for each friend's meeting start and end times
    for friend in friends:
        friend["z3_start"] = Int(f"{friend['name']}_start")
        friend["z3_end"] = Int(f"{friend['name']}_end")
        s.add(friend["z3_start"] >= friend["start_min"])
        s.add(friend["z3_end"] <= friend["end_min"])
        s.add(friend["z3_end"] - friend["z3_start"] >= friend["duration"])

    # Add constraints for travel times between meetings
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            # Ensure no overlap between meetings considering travel time
            travel_time = travel_times.get((friends[i]["location"], friends[j]["location"]), 0)
            s.add(Or(
                friends[i]["z3_end"] + travel_time <= friends[j]["z3_start"],
                friends[j]["z3_end"] + travel_time <= friends[i]["z3_start"]
            ))

    # Try to maximize the number of friends met
    # This is a simplified approach; a more sophisticated one would use optimization
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            start = m.evaluate(friend["z3_start"]).as_long()
            end = m.evaluate(friend["z3_end"]).as_long()
            if start >= 0 and end > start:
                start_hour = (start + 540) // 60
                start_min = (start + 540) % 60
                end_hour = (end + 540) // 60
                end_min = (end + 540) % 60
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": f"{start_hour:02d}:{start_min:02d}",
                    "end_time": f"{end_hour:02d}:{end_min:02d}"
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))