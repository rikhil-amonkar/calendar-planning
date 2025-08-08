from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Stephanie": {
            "location": "Russian Hill",
            "available_start": "20:00",
            "available_end": "20:45",
            "min_duration": 15,
        },
        "Kevin": {
            "location": "Fisherman's Wharf",
            "available_start": "19:15",
            "available_end": "21:45",
            "min_duration": 75,
        },
        "Robert": {
            "location": "Nob Hill",
            "available_start": "07:45",
            "available_end": "10:30",
            "min_duration": 90,
        },
        "Steven": {
            "location": "Golden Gate Park",
            "available_start": "08:30",
            "available_end": "17:00",
            "min_duration": 75,
        },
        "Anthony": {
            "location": "Alamo Square",
            "available_start": "07:45",
            "available_end": "19:45",
            "min_duration": 15,
        },
        "Sandra": {
            "location": "Pacific Heights",
            "available_start": "14:45",
            "available_end": "21:45",
            "min_duration": 45,
        }
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

    # Define travel times between locations (in minutes)
    travel_times = {
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
    }

    # Current location starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_location = "Haight-Ashbury"
    current_time = time_to_minutes("09:00")

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = (start, end)

    # Add constraints for each friend
    for name, info in friends.items():
        start, end = meeting_vars[name]
        available_start = time_to_minutes(info["available_start"])
        available_end = time_to_minutes(info["available_end"])
        min_duration = info["min_duration"]

        # Meeting must start and end within the available window
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + min_duration)

    # Define the order of meetings and travel times
    # We need to sequence meetings and account for travel times
    # This is complex; we'll try to find a feasible order
    # For simplicity, we'll assume a fixed order and check feasibility
    # Alternatively, we can use a more sophisticated approach with Z3's sequencing

    # For this problem, we'll prioritize meetings that are time-sensitive
    # Let's try to meet Robert first (since his window is early)
    # Then Steven, Anthony, Sandra, Kevin, Stephanie

    # Define the order: Robert, Steven, Anthony, Sandra, Kevin, Stephanie
    order = ["Robert", "Steven", "Anthony", "Sandra", "Kevin", "Stephanie"]

    # Add constraints for travel times between meetings
    prev_location = current_location
    prev_end = current_time
    for name in order:
        start, end = meeting_vars[name]
        location = friends[name]["location"]
        travel_time = travel_times.get((prev_location, location), 0)
        s.add(start >= prev_end + travel_time)
        prev_location = location
        prev_end = end

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start, end = meeting_vars[name]
            start_val = model.evaluate(start).as_long()
            end_val = model.evaluate(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))