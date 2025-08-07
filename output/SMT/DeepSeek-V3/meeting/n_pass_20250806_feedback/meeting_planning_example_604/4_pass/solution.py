from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their constraints
    friends = [
        {"name": "Laura", "location": "The Castro", "available_start": "19:45", "available_end": "21:30", "min_duration": 105},
        {"name": "Daniel", "location": "Golden Gate Park", "available_start": "21:15", "available_end": "21:45", "min_duration": 15},
        {"name": "William", "location": "Embarcadero", "available_start": "07:00", "available_end": "09:00", "min_duration": 90},
        {"name": "Karen", "location": "Russian Hill", "available_start": "14:30", "available_end": "19:45", "min_duration": 30},
        {"name": "Stephanie", "location": "Nob Hill", "available_start": "07:30", "available_end": "09:30", "min_duration": 45},
        {"name": "Joseph", "location": "Alamo Square", "available_start": "11:30", "available_end": "12:45", "min_duration": 15},
        {"name": "Kimberly", "location": "North Beach", "available_start": "15:45", "available_end": "19:15", "min_duration": 30}
    ]

    # Convert time strings to minutes since 00:00
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for friend in friends:
        name = friend["name"]
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = (start_var, end_var)

    # Add constraints for each friend
    for friend in friends:
        name = friend["name"]
        start_var, end_var = meeting_vars[name]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Meeting must start and end within the available window
        s.add(start_var >= available_start)
        s.add(end_var <= available_end)
        # Meeting duration must be at least min_duration
        s.add(end_var - start_var >= min_duration)
        # Start time must be before end time
        s.add(start_var < end_var)

    # Define travel times dictionary
    travel_times = {
        ("Fisherman's Wharf", "The Castro"): 26,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "North Beach"): 20,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "North Beach"): 24,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "North Beach"): 5,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "North Beach"): 5,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Alamo Square"): 16
    }

    # Current location starts at Fisherman's Wharf at 9:00 AM (540 minutes)
    current_time = time_to_minutes("09:00")
    current_location = "Fisherman's Wharf"

    # Define the order of meetings to try
    # We'll try to meet Joseph, Karen, Kimberly, Laura, Daniel
    # as they have the most flexible time windows
    meeting_order = ["Joseph", "Karen", "Kimberly", "Laura", "Daniel"]

    # Add constraints for travel times between meetings
    for i in range(len(meeting_order)):
        if i == 0:
            # First meeting: travel from Fisherman's Wharf to the first friend's location
            friend_name = meeting_order[i]
            friend_loc = next(f["location"] for f in friends if f["name"] == friend_name)
            travel_time = travel_times[(current_location, friend_loc)]
            start_var, end_var = meeting_vars[friend_name]
            s.add(start_var >= current_time + travel_time)
        else:
            # Subsequent meetings: travel from previous friend's location to current friend's location
            prev_friend_name = meeting_order[i-1]
            prev_friend_loc = next(f["location"] for f in friends if f["name"] == prev_friend_name)
            friend_name = meeting_order[i]
            friend_loc = next(f["location"] for f in friends if f["name"] == friend_name)
            travel_time = travel_times[(prev_friend_loc, friend_loc)]
            prev_start, prev_end = meeting_vars[prev_friend_name]
            start_var, end_var = meeting_vars[friend_name]
            s.add(start_var >= prev_end + travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            start_var, end_var = meeting_vars[name]
            start_time = model.evaluate(start_var)
            end_time = model.evaluate(end_var)
            if isinstance(start_time, IntNumRef) and isinstance(end_time, IntNumRef):
                start_min = start_time.as_long()
                end_min = end_time.as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_min),
                    "end_time": minutes_to_time(end_min)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))