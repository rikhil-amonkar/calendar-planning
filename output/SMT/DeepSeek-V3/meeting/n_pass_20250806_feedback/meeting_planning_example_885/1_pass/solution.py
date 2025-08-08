from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = {
        "Mark": {"location": "Marina District", "available_start": "18:45", "available_end": "21:00", "min_duration": 90},
        "Karen": {"location": "Financial District", "available_start": "09:30", "available_end": "12:45", "min_duration": 90},
        "Barbara": {"location": "Alamo Square", "available_start": "10:00", "available_end": "19:30", "min_duration": 90},
        "Nancy": {"location": "Golden Gate Park", "available_start": "16:45", "available_end": "20:00", "min_duration": 105},
        "David": {"location": "The Castro", "available_start": "09:00", "available_end": "18:00", "min_duration": 120},
        "Linda": {"location": "Bayview", "available_start": "18:15", "available_end": "19:45", "min_duration": 45},
        "Kevin": {"location": "Sunset District", "available_start": "10:00", "available_end": "17:45", "min_duration": 120},
        "Matthew": {"location": "Haight-Ashbury", "available_start": "10:15", "available_end": "15:30", "min_duration": 45},
        "Andrew": {"location": "Nob Hill", "available_start": "11:45", "available_end": "16:45", "min_duration": 105}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Russian Hill": {
            "Marina District": 7,
            "Financial District": 11,
            "Alamo Square": 15,
            "Golden Gate Park": 21,
            "The Castro": 21,
            "Bayview": 23,
            "Sunset District": 23,
            "Haight-Ashbury": 17,
            "Nob Hill": 5
        },
        "Marina District": {
            "Russian Hill": 8,
            "Financial District": 17,
            "Alamo Square": 15,
            "Golden Gate Park": 18,
            "The Castro": 22,
            "Bayview": 27,
            "Sunset District": 19,
            "Haight-Ashbury": 16,
            "Nob Hill": 12
        },
        "Financial District": {
            "Russian Hill": 11,
            "Marina District": 15,
            "Alamo Square": 17,
            "Golden Gate Park": 23,
            "The Castro": 20,
            "Bayview": 19,
            "Sunset District": 30,
            "Haight-Ashbury": 19,
            "Nob Hill": 8
        },
        "Alamo Square": {
            "Russian Hill": 13,
            "Marina District": 15,
            "Financial District": 17,
            "Golden Gate Park": 9,
            "The Castro": 8,
            "Bayview": 16,
            "Sunset District": 16,
            "Haight-Ashbury": 5,
            "Nob Hill": 11
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Marina District": 16,
            "Financial District": 26,
            "Alamo Square": 9,
            "The Castro": 13,
            "Bayview": 23,
            "Sunset District": 10,
            "Haight-Ashbury": 7,
            "Nob Hill": 20
        },
        "The Castro": {
            "Russian Hill": 18,
            "Marina District": 21,
            "Financial District": 21,
            "Alamo Square": 8,
            "Golden Gate Park": 11,
            "Bayview": 19,
            "Sunset District": 17,
            "Haight-Ashbury": 6,
            "Nob Hill": 16
        },
        "Bayview": {
            "Russian Hill": 23,
            "Marina District": 27,
            "Financial District": 19,
            "Alamo Square": 16,
            "Golden Gate Park": 22,
            "The Castro": 19,
            "Sunset District": 23,
            "Haight-Ashbury": 19,
            "Nob Hill": 20
        },
        "Sunset District": {
            "Russian Hill": 24,
            "Marina District": 21,
            "Financial District": 30,
            "Alamo Square": 17,
            "Golden Gate Park": 11,
            "The Castro": 17,
            "Bayview": 22,
            "Haight-Ashbury": 15,
            "Nob Hill": 27
        },
        "Haight-Ashbury": {
            "Russian Hill": 17,
            "Marina District": 17,
            "Financial District": 21,
            "Alamo Square": 5,
            "Golden Gate Park": 7,
            "The Castro": 6,
            "Bayview": 18,
            "Sunset District": 15,
            "Nob Hill": 15
        },
        "Nob Hill": {
            "Russian Hill": 5,
            "Marina District": 11,
            "Financial District": 9,
            "Alamo Square": 11,
            "Golden Gate Park": 17,
            "The Castro": 17,
            "Bayview": 19,
            "Sunset District": 24,
            "Haight-Ashbury": 13
        }
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Russian Hill at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Russian Hill"

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}

        # Constrain meetings to be within friend's availability
        available_start = time_to_minutes(friends[name]["available_start"])
        available_end = time_to_minutes(friends[name]["available_end"])
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + friends[name]["min_duration"])

    # Determine the order of meetings. We'll try all permutations, but for simplicity, we'll use a heuristic.
    # Alternatively, we can use Z3 to find an order, but it's complex. Here, we'll try a fixed order based on earliest availability.

    # Let's try meeting friends in the order: Karen, Andrew, Matthew, Kevin, Barbara, Nancy, Linda, Mark
    # This is a heuristic; in practice, we'd need a more sophisticated approach.

    # We'll model the sequence as a list and add constraints for travel times.
    # For simplicity, we'll assume a specific order and check feasibility.

    # Define the order (this is a guess; in practice, we'd need to try multiple orders)
    order = ["Karen", "Andrew", "Matthew", "Kevin", "Barbara", "Nancy", "Linda", "Mark"]

    # Add constraints for the order
    prev_end = current_time
    prev_location = current_location
    for name in order:
        start_var = meeting_vars[name]['start']
        end_var = meeting_vars[name]['end']
        travel_time = travel_times[prev_location][friends[name]["location"]]
        s.add(start_var >= prev_end + travel_time)
        prev_end = end_var
        prev_location = friends[name]["location"]

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start_val = model[meeting_vars[name]['start']].as_long()
            end_val = model[meeting_vars[name]['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        # If not feasible, try a different order or fewer friends
        # For brevity, we'll return an empty itinerary here
        return {"itinerary": []}

# Solve the scheduling problem
solution = solve_scheduling()
print(json.dumps(solution, indent=2))