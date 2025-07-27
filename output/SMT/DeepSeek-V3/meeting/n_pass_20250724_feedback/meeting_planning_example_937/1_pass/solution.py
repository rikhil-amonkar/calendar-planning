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

    # Define travel times (simplified as a dictionary of dictionaries)
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
        # Other locations can be added similarly if needed
    }

    # Define the order of meetings (simplified approach)
    # We'll try to meet friends in an order that minimizes travel time
    # This is a heuristic; a more complete solution would consider all permutations
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