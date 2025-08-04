from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Laura": {"location": "The Castro", "start": "19:45", "end": "21:30", "min_duration": 105},
        "Daniel": {"location": "Golden Gate Park", "start": "21:15", "end": "21:45", "min_duration": 15},
        "William": {"location": "Embarcadero", "start": "07:00", "end": "09:00", "min_duration": 90},
        "Karen": {"location": "Russian Hill", "start": "14:30", "end": "19:45", "min_duration": 30},
        "Stephanie": {"location": "Nob Hill", "start": "07:30", "end": "09:30", "min_duration": 45},
        "Joseph": {"location": "Alamo Square", "start": "11:30", "end": "12:45", "min_duration": 15},
        "Kimberly": {"location": "North Beach", "start": "15:45", "end": "19:15", "min_duration": 30}
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

    # Initialize variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"{name}_start")
        end_var = Int(f"{name}_end")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Current location starts at Fisherman's Wharf at 9:00 AM (540 minutes)
    current_location = "Fisherman's Wharf"
    current_time = 540  # 9:00 AM in minutes

    # Define the travel times dictionary
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

    # Constraints for each friend's meeting time
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]

        s.add(meeting_vars[name]["start"] >= start_min)
        s.add(meeting_vars[name]["end"] <= end_min)
        s.add(meeting_vars[name]["end"] - meeting_vars[name]["start"] >= min_duration)

    # Define the order of meetings and travel times
    # We'll try to meet as many friends as possible in a feasible sequence
    # Let's try to meet Joseph, Karen, Kimberly, Laura, and Daniel
    sequence = ["Joseph", "Karen", "Kimberly", "Laura", "Daniel"]

    # Current time is 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Fisherman's Wharf"
    itinerary = []

    for name in sequence:
        friend = friends[name]
        location = friend["location"]
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + travel_time
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]

        # The meeting can start at max(start_window, arrival_time)
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + min_duration

        # Check if meeting_end is within the window
        if meeting_end > end_window:
            # This sequence is not feasible; skip
            continue

        # Add to itinerary
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

        # Update current time and location
        current_time = meeting_end
        current_location = location

    # Output the itinerary
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

solve_scheduling()