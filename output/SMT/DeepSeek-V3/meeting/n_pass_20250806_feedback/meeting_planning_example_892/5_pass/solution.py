import json
from z3 import *

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define friends and their constraints
    friends = {
        "Charles": {"location": "Bayview", "available_start": "11:30", "available_end": "14:30", "min_duration": 45},
        "Robert": {"location": "Sunset District", "available_start": "16:45", "available_end": "21:00", "min_duration": 30},
        "Karen": {"location": "Richmond District", "available_start": "19:15", "available_end": "21:30", "min_duration": 60},
        "Rebecca": {"location": "Nob Hill", "available_start": "16:15", "available_end": "20:30", "min_duration": 90},
        "Margaret": {"location": "Chinatown", "available_start": "14:15", "available_end": "19:45", "min_duration": 120},
        "Patricia": {"location": "Haight-Ashbury", "available_start": "14:30", "available_end": "20:30", "min_duration": 45},
        "Mark": {"location": "North Beach", "available_start": "14:00", "available_end": "18:30", "min_duration": 105},
        "Melissa": {"location": "Russian Hill", "available_start": "13:00", "available_end": "19:45", "min_duration": 30},
        "Laura": {"location": "Embarcadero", "available_start": "07:45", "available_end": "13:15", "min_duration": 105}
    }

    # Complete travel times dictionary
    travel_times = {
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Embarcadero"): 14,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Embarcadero"): 19,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Embarcadero"): 30,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Embarcadero"): 19,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Embarcadero"): 9,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Embarcadero"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Embarcadero"): 6,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Embarcadero"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Russian Hill"): 8
    }

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = {"start": start, "end": end}

    # Add constraints for each friend
    for name, data in friends.items():
        start_var = meeting_vars[name]["start"]
        end_var = meeting_vars[name]["end"]
        available_start = time_to_minutes(data["available_start"])
        available_end = time_to_minutes(data["available_end"])
        min_duration = data["min_duration"]

        # Meeting must be within available time
        solver.add(start_var >= available_start)
        solver.add(end_var <= available_end)
        solver.add(end_var >= start_var + min_duration)

        # Ensure all meetings start at or after 9:00 AM (540 minutes)
        solver.add(start_var >= 540)

    # Starting point is Marina District at 9:00 AM
    current_location = "Marina District"
    current_time = 540  # 9:00 AM in minutes

    # Create a list of all friends to meet
    friend_names = list(friends.keys())

    # Create variables to represent the order of meetings
    order = {name: Int(f"order_{name}") for name in friend_names}
    for name in friend_names:
        solver.add(order[name] >= 0, order[name] < len(friend_names))

    # All orders must be distinct
    solver.add(Distinct([order[name] for name in friend_names]))

    # Add travel time constraints between consecutive meetings
    for i in range(len(friend_names)):
        for j in range(len(friend_names)):
            if i != j:
                # If meeting i comes right before meeting j
                solver.add(Implies(
                    order[friend_names[i]] + 1 == order[friend_names[j]],
                    meeting_vars[friend_names[j]]["start"] >= meeting_vars[friend_names[i]]["end"] + 
                    travel_times[(friends[friend_names[i]]["location"], friends[friend_names[j]]["location"])]
                ))

    # First meeting must account for travel from Marina District
    for name in friend_names:
        solver.add(Implies(
            order[name] == 0,
            meeting_vars[name]["start"] >= current_time + travel_times[(current_location, friends[name]["location"])]
        ))

    # Try to maximize the number of friends met
    # This is a simplified approach - a full solution would need to optimize the order
    if solver.check() == sat:
        model = solver.model()
        # Extract the schedule
        itinerary = []
        for name in friend_names:
            start_val = model[meeting_vars[name]["start"]].as_long()
            end_val = model[meeting_vars[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val),
                "location": friends[name]["location"]
            })

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: model[order[x["person"]]].as_long())
        return {"itinerary": [{"action": x["action"], "person": x["person"], 
                             "start_time": x["start_time"], "end_time": x["end_time"]} 
                            for x in itinerary]}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))