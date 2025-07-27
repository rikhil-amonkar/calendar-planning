from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {"name": "David", "location": "Sunset District", "available_start": "09:15", "available_end": "22:00", "min_duration": 15},
        {"name": "Kenneth", "location": "Union Square", "available_start": "21:15", "available_end": "21:45", "min_duration": 15},
        {"name": "Patricia", "location": "Nob Hill", "available_start": "15:00", "available_end": "19:15", "min_duration": 120},
        {"name": "Mary", "location": "Marina District", "available_start": "14:45", "available_end": "16:45", "min_duration": 45},
        {"name": "Charles", "location": "Richmond District", "available_start": "17:15", "available_end": "21:00", "min_duration": 15},
        {"name": "Joshua", "location": "Financial District", "available_start": "14:30", "available_end": "17:15", "min_duration": 90},
        {"name": "Ronald", "location": "Embarcadero", "available_start": "18:15", "available_end": "20:45", "min_duration": 30},
        {"name": "George", "location": "The Castro", "available_start": "14:15", "available_end": "19:00", "min_duration": 105},
        {"name": "Kimberly", "location": "Alamo Square", "available_start": "09:00", "available_end": "14:30", "min_duration": 105},
        {"name": "William", "location": "Presidio", "available_start": "07:00", "available_end": "12:45", "min_duration": 60}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times
    for friend in friends:
        friend["start_var"] = Int(f"start_{friend['name']}")
        friend["end_var"] = Int(f"end_{friend['name']}")
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Add constraints for each friend's meeting time
        s.add(friend["start_var"] >= available_start)
        s.add(friend["end_var"] <= available_end)
        s.add(friend["end_var"] >= friend["start_var"] + min_duration)

    # Define the current location and time
    current_location = "Russian Hill"
    current_time = time_to_minutes("09:00")

    # Define travel times (complete dictionary of dictionaries)
    travel_times = {
        "Russian Hill": {
            "Sunset District": 23,
            "Union Square": 10,
            "Nob Hill": 5,
            "Marina District": 7,
            "Richmond District": 14,
            "Financial District": 11,
            "Embarcadero": 8,
            "The Castro": 21,
            "Alamo Square": 15,
            "Presidio": 14
        },
        "Sunset District": {
            "Russian Hill": 24,
            "Union Square": 30,
            "Nob Hill": 27,
            "Marina District": 21,
            "Richmond District": 12,
            "Financial District": 30,
            "Embarcadero": 30,
            "The Castro": 17,
            "Alamo Square": 17,
            "Presidio": 16
        },
        "Union Square": {
            "Russian Hill": 13,
            "Sunset District": 27,
            "Nob Hill": 9,
            "Marina District": 18,
            "Richmond District": 20,
            "Financial District": 9,
            "Embarcadero": 11,
            "The Castro": 17,
            "Alamo Square": 15,
            "Presidio": 24
        },
        "Nob Hill": {
            "Russian Hill": 5,
            "Sunset District": 24,
            "Union Square": 7,
            "Marina District": 11,
            "Richmond District": 14,
            "Financial District": 9,
            "Embarcadero": 9,
            "The Castro": 17,
            "Alamo Square": 11,
            "Presidio": 17
        },
        "Marina District": {
            "Russian Hill": 8,
            "Sunset District": 19,
            "Union Square": 16,
            "Nob Hill": 12,
            "Richmond District": 11,
            "Financial District": 17,
            "Embarcadero": 14,
            "The Castro": 22,
            "Alamo Square": 15,
            "Presidio": 10
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Sunset District": 11,
            "Union Square": 21,
            "Nob Hill": 17,
            "Marina District": 9,
            "Financial District": 22,
            "Embarcadero": 19,
            "The Castro": 16,
            "Alamo Square": 13,
            "Presidio": 7
        },
        "Financial District": {
            "Russian Hill": 11,
            "Sunset District": 30,
            "Union Square": 9,
            "Nob Hill": 8,
            "Marina District": 15,
            "Richmond District": 21,
            "Embarcadero": 4,
            "The Castro": 20,
            "Alamo Square": 17,
            "Presidio": 22
        },
        "Embarcadero": {
            "Russian Hill": 8,
            "Sunset District": 30,
            "Union Square": 10,
            "Nob Hill": 10,
            "Marina District": 12,
            "Richmond District": 21,
            "Financial District": 5,
            "The Castro": 25,
            "Alamo Square": 19,
            "Presidio": 20
        },
        "The Castro": {
            "Russian Hill": 18,
            "Sunset District": 17,
            "Union Square": 19,
            "Nob Hill": 16,
            "Marina District": 21,
            "Richmond District": 16,
            "Financial District": 21,
            "Embarcadero": 22,
            "Alamo Square": 8,
            "Presidio": 20
        },
        "Alamo Square": {
            "Russian Hill": 13,
            "Sunset District": 16,
            "Union Square": 14,
            "Nob Hill": 11,
            "Marina District": 15,
            "Richmond District": 11,
            "Financial District": 17,
            "Embarcadero": 16,
            "The Castro": 8,
            "Presidio": 17
        },
        "Presidio": {
            "Russian Hill": 14,
            "Sunset District": 15,
            "Union Square": 22,
            "Nob Hill": 18,
            "Marina District": 11,
            "Richmond District": 7,
            "Financial District": 23,
            "Embarcadero": 20,
            "The Castro": 21,
            "Alamo Square": 19
        }
    }

    # Define the order of meetings (simplified heuristic)
    meeting_order = ["Kimberly", "William", "David", "Mary", "Joshua", "Patricia", "George", "Ronald", "Charles", "Kenneth"]

    # Add constraints for travel times between meetings
    for i in range(len(meeting_order) - 1):
        current_friend = next(f for f in friends if f["name"] == meeting_order[i])
        next_friend = next(f for f in friends if f["name"] == meeting_order[i+1])
        travel_time = travel_times[current_friend["location"]][next_friend["location"]]
        s.add(next_friend["start_var"] >= current_friend["end_var"] + travel_time)

    # Ensure the first meeting starts after arrival time plus travel time
    first_friend = next(f for f in friends if f["name"] == meeting_order[0])
    travel_time = travel_times[current_location][first_friend["location"]]
    s.add(first_friend["start_var"] >= current_time + travel_time)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            start = model.evaluate(friend["start_var"]).as_long()
            end = model.evaluate(friend["end_var"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))