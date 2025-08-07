from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Carol", "location": "Haight-Ashbury", "available_start": "21:30", "available_end": "22:30", "min_duration": 60},
        {"name": "Laura", "location": "Fisherman's Wharf", "available_start": "11:45", "available_end": "21:30", "min_duration": 60},
        {"name": "Karen", "location": "The Castro", "available_start": "07:15", "available_end": "14:00", "min_duration": 75},
        {"name": "Elizabeth", "location": "Chinatown", "available_start": "12:15", "available_end": "21:30", "min_duration": 75},
        {"name": "Deborah", "location": "Alamo Square", "available_start": "12:00", "available_end": "15:00", "min_duration": 105},
        {"name": "Jason", "location": "North Beach", "available_start": "14:45", "available_end": "19:00", "min_duration": 90},
        {"name": "Steven", "location": "Russian Hill", "available_start": "14:45", "available_end": "18:30", "min_duration": 120}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location is Golden Gate Park at 9:00 AM (540 minutes)
    initial_time = time_to_minutes("09:00")
    current_location = "Golden Gate Park"

    # Travel times dictionary: from -> to -> minutes
    travel_times = {
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Fisherman's Wharf": 24,
            "The Castro": 13,
            "Chinatown": 23,
            "Alamo Square": 10,
            "North Beach": 24,
            "Russian Hill": 19
        },
        "Haight-Ashbury": {
            "Golden Gate Park": 7,
            "Fisherman's Wharf": 23,
            "The Castro": 6,
            "Chinatown": 19,
            "Alamo Square": 5,
            "North Beach": 19,
            "Russian Hill": 17
        },
        "Fisherman's Wharf": {
            "Golden Gate Park": 25,
            "Haight-Ashbury": 22,
            "The Castro": 26,
            "Chinatown": 12,
            "Alamo Square": 20,
            "North Beach": 6,
            "Russian Hill": 7
        },
        "The Castro": {
            "Golden Gate Park": 11,
            "Haight-Ashbury": 6,
            "Fisherman's Wharf": 24,
            "Chinatown": 20,
            "Alamo Square": 8,
            "North Beach": 20,
            "Russian Hill": 18
        },
        "Chinatown": {
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Fisherman's Wharf": 8,
            "The Castro": 22,
            "Alamo Square": 17,
            "North Beach": 3,
            "Russian Hill": 7
        },
        "Alamo Square": {
            "Golden Gate Park": 9,
            "Haight-Ashbury": 5,
            "Fisherman's Wharf": 19,
            "The Castro": 8,
            "Chinatown": 16,
            "North Beach": 15,
            "Russian Hill": 13
        },
        "North Beach": {
            "Golden Gate Park": 22,
            "Haight-Ashbury": 18,
            "Fisherman's Wharf": 5,
            "The Castro": 22,
            "Chinatown": 6,
            "Alamo Square": 16,
            "Russian Hill": 4
        },
        "Russian Hill": {
            "Golden Gate Park": 21,
            "Haight-Ashbury": 17,
            "Fisherman's Wharf": 7,
            "The Castro": 21,
            "Chinatown": 9,
            "Alamo Square": 15,
            "North Beach": 5
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        duration = friend["min_duration"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        
        # Add constraints for meeting times
        s.add(start_var >= available_start)
        s.add(end_var <= available_end)
        s.add(end_var == start_var + duration)
        
        meeting_vars.append({
            "name": friend["name"],
            "location": friend["location"],
            "start_var": start_var,
            "end_var": end_var
        })

    # To handle sequencing, we need to define an order of meetings.
    # This is a complex part; for simplicity, we'll try to meet friends in order of their available_end times.
    ordered_friends = sorted(friends, key=lambda x: time_to_minutes(x["available_end"]))
    prev_end = initial_time
    prev_location = current_location

    for friend in ordered_friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        travel_time = travel_times[prev_location][friend["location"]]
        
        # The start time must be >= previous end time + travel time
        s.add(start_var >= prev_end + travel_time)
        
        prev_end = end_var
        prev_location = friend["location"]

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            start_val = model.evaluate(Int(f"start_{friend['name']}")).as_long()
            end_val = model.evaluate(Int(f"end_{friend['name']}")).as_long()
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))