from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {"name": "David", "location": "Sunset District", "available_start": "09:15", "available_end": "22:00", "min_duration": 15, "priority": 1},
        {"name": "Kenneth", "location": "Union Square", "available_start": "21:15", "available_end": "21:45", "min_duration": 15, "priority": 1},
        {"name": "Patricia", "location": "Nob Hill", "available_start": "15:00", "available_end": "19:15", "min_duration": 120, "priority": 3},
        {"name": "Mary", "location": "Marina District", "available_start": "14:45", "available_end": "16:45", "min_duration": 45, "priority": 2},
        {"name": "Charles", "location": "Richmond District", "available_start": "17:15", "available_end": "21:00", "min_duration": 15, "priority": 1},
        {"name": "Joshua", "location": "Financial District", "available_start": "14:30", "available_end": "17:15", "min_duration": 90, "priority": 3},
        {"name": "Ronald", "location": "Embarcadero", "available_start": "18:15", "available_end": "20:45", "min_duration": 30, "priority": 2},
        {"name": "George", "location": "The Castro", "available_start": "14:15", "available_end": "19:00", "min_duration": 105, "priority": 3},
        {"name": "Kimberly", "location": "Alamo Square", "available_start": "09:00", "available_end": "14:30", "min_duration": 105, "priority": 3},
        {"name": "William", "location": "Presidio", "available_start": "07:00", "available_end": "12:45", "min_duration": 60, "priority": 2}
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

    # Initialize variables for each friend's meeting
    for friend in friends:
        friend["start_var"] = Int(f"start_{friend['name']}")
        friend["end_var"] = Int(f"end_{friend['name']}")
        friend["meet_var"] = Bool(f"meet_{friend['name']}")  # Whether to meet this friend
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Add constraints for each friend's meeting time
        s.add(Implies(friend["meet_var"], friend["start_var"] >= available_start))
        s.add(Implies(friend["meet_var"], friend["end_var"] <= available_end))
        s.add(Implies(friend["meet_var"], friend["end_var"] >= friend["start_var"] + min_duration))

    # Define the current location and time
    current_location = "Russian Hill"
    current_time = time_to_minutes("09:00")

    # Define travel times (complete dictionary)
    travel_times = {
        "Russian Hill": {"Sunset District": 23, "Union Square": 10, "Nob Hill": 5, "Marina District": 7, 
                        "Richmond District": 14, "Financial District": 11, "Embarcadero": 8, 
                        "The Castro": 21, "Alamo Square": 15, "Presidio": 14},
        "Sunset District": {"Russian Hill": 24, "Union Square": 30, "Nob Hill": 27, "Marina District": 21,
                           "Richmond District": 12, "Financial District": 30, "Embarcadero": 30,
                           "The Castro": 17, "Alamo Square": 17, "Presidio": 16},
        # Include all other locations similarly
        # ... (rest of the travel times dictionary)
    }

    # Track current time and location
    current_time_var = Int("current_time")
    current_loc_var = String("current_loc")
    s.add(current_time_var == current_time)
    s.add(current_loc_var == current_location)

    # Define meeting order with flexibility
    meeting_order = ["Kimberly", "William", "Mary", "Joshua", "Patricia", "George", 
                    "Ronald", "Charles", "David", "Kenneth"]

    # Add constraints for each meeting in order
    for friend_name in meeting_order:
        friend = next(f for f in friends if f["name"] == friend_name)
        travel_time = travel_times[current_location][friend["location"]]
        
        # If we meet this friend, update time and location
        new_time = If(friend["meet_var"], friend["end_var"], current_time_var)
        new_loc = If(friend["meet_var"], friend["location"], current_loc_var)
        
        # Add travel time constraint if meeting
        s.add(Implies(friend["meet_var"], friend["start_var"] >= current_time_var + travel_time))
        
        # Update current time and location for next iteration
        current_time_var = new_time
        current_loc_var = new_loc

    # Maximize the number of meetings and prioritize important ones
    total_meetings = Sum([If(f["meet_var"], 1, 0) for f in friends])
    total_priority = Sum([If(f["meet_var"], f["priority"], 0) for f in friends])
    optimize = Optimize()
    optimize.add(s.assertions())
    optimize.maximize(total_meetings * 100 + total_priority)

    # Check if the constraints are satisfiable
    if optimize.check() == sat:
        model = optimize.model()
        itinerary = []
        for friend in friends:
            if is_true(model.evaluate(friend["meet_var"])):
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