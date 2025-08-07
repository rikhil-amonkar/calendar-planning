from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Kevin": {"location": "Mission District", "start": "20:45", "end": "21:45", "duration": 60},
        "Mark": {"location": "Fisherman's Wharf", "start": "17:15", "end": "20:00", "duration": 90},
        "Jessica": {"location": "Russian Hill", "start": "09:00", "end": "15:00", "duration": 120},
        "Jason": {"location": "Marina District", "start": "15:15", "end": "21:45", "duration": 120},
        "John": {"location": "North Beach", "start": "09:45", "end": "18:00", "duration": 15},
        "Karen": {"location": "Chinatown", "start": "16:45", "end": "19:00", "duration": 75},
        "Sarah": {"location": "Pacific Heights", "start": "17:30", "end": "18:15", "duration": 45},
        "Amanda": {"location": "The Castro", "start": "20:00", "end": "21:15", "duration": 60},
        "Nancy": {"location": "Nob Hill", "start": "09:45", "end": "13:00", "duration": 45},
        "Rebecca": {"location": "Sunset District", "start": "08:45", "end": "15:00", "duration": 75}
    }

    # Travel times dictionary (simplified for this example)
    travel_times = {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        # Add other travel times as needed
    }

    # Function to convert time string to minutes
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert friends' availability to minutes
    for name, data in friends.items():
        data["start_min"] = time_to_minutes(data["start"])
        data["end_min"] = time_to_minutes(data["end"])

    # Current location starts at Union Square at 9:00 AM (540 minutes)
    current_location = "Union Square"
    current_time = time_to_minutes("09:00")

    itinerary = []

    # Sort friends by their availability start time
    sorted_friends = sorted(friends.items(), key=lambda x: x[1]["start_min"])

    # Try to schedule each friend in order
    for name, data in sorted_friends:
        location = data["location"]
        duration = data["duration"]
        start_window = data["start_min"]
        end_window = data["end_min"]

        # Calculate travel time from current location
        travel_time = travel_times.get((current_location, location), 0)

        # Earliest possible start time after travel
        earliest_start = current_time + travel_time

        # Latest possible start time to meet duration
        latest_start = end_window - duration

        # Check if meeting is possible
        if earliest_start <= latest_start and earliest_start >= start_window:
            # Schedule the meeting
            start_time = earliest_start
            end_time = start_time + duration

            # Add to itinerary
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_time // 60:02d}:{start_time % 60:02d}",
                "end_time": f"{end_time // 60:02d}:{end_time % 60:02d}"
            })

            # Update current location and time
            current_location = location
            current_time = end_time

    # Ensure we meet Kevin for at least 60 minutes (special case since it's late)
    kevin_data = friends["Kevin"]
    kevin_start = kevin_data["start_min"]
    kevin_end = kevin_data["end_min"]
    kevin_duration = kevin_data["duration"]
    travel_time = travel_times.get((current_location, "Mission District"), 0)

    if current_time + travel_time <= kevin_end - kevin_duration:
        kevin_meet_start = max(current_time + travel_time, kevin_start)
        kevin_meet_end = kevin_meet_start + kevin_duration

        itinerary.append({
            "action": "meet",
            "person": "Kevin",
            "start_time": f"{kevin_meet_start // 60:02d}:{kevin_meet_start % 60:02d}",
            "end_time": f"{kevin_meet_end // 60:02d}:{kevin_meet_end % 60:02d}"
        })

    return {"itinerary": itinerary}

# Solve the problem
solution = solve_scheduling_problem()

# Print the solution in JSON format
print(json.dumps(solution, indent=2))