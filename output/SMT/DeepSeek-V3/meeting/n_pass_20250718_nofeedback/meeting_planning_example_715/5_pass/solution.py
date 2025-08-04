from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Amanda", "location": "Marina District", "available_start": "14:45", "available_end": "19:30", "min_duration": 105},
        {"name": "Melissa", "location": "The Castro", "available_start": "09:30", "available_end": "17:00", "min_duration": 30},
        {"name": "Jeffrey", "location": "Fisherman's Wharf", "available_start": "12:45", "available_end": "18:45", "min_duration": 120},
        {"name": "Matthew", "location": "Bayview", "available_start": "10:15", "available_end": "13:15", "min_duration": 30},
        {"name": "Nancy", "location": "Pacific Heights", "available_start": "17:00", "available_end": "21:30", "min_duration": 105},
        {"name": "Karen", "location": "Mission District", "available_start": "17:30", "available_end": "20:30", "min_duration": 105},
        {"name": "Robert", "location": "Alamo Square", "available_start": "11:15", "available_end": "17:30", "min_duration": 120},
        {"name": "Joseph", "location": "Golden Gate Park", "available_start": "08:30", "available_end": "21:15", "min_duration": 105}
    ]

    # Define travel times (in minutes) between locations
    travel_times = {
        "Presidio": {
            "Marina District": 11,
            "The Castro": 21,
            "Fisherman's Wharf": 19,
            "Bayview": 31,
            "Pacific Heights": 11,
            "Mission District": 26,
            "Alamo Square": 19,
            "Golden Gate Park": 12
        },
        "Marina District": {
            "Presidio": 10,
            "The Castro": 22,
            "Fisherman's Wharf": 10,
            "Bayview": 27,
            "Pacific Heights": 7,
            "Mission District": 20,
            "Alamo Square": 15,
            "Golden Gate Park": 18
        },
        "The Castro": {
            "Presidio": 20,
            "Marina District": 21,
            "Fisherman's Wharf": 24,
            "Bayview": 19,
            "Pacific Heights": 16,
            "Mission District": 7,
            "Alamo Square": 8,
            "Golden Gate Park": 11
        },
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Marina District": 9,
            "The Castro": 27,
            "Bayview": 26,
            "Pacific Heights": 12,
            "Mission District": 22,
            "Alamo Square": 21,
            "Golden Gate Park": 25
        },
        "Bayview": {
            "Presidio": 32,
            "Marina District": 27,
            "The Castro": 19,
            "Fisherman's Wharf": 25,
            "Pacific Heights": 23,
            "Mission District": 13,
            "Alamo Square": 16,
            "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "Presidio": 11,
            "Marina District": 6,
            "The Castro": 16,
            "Fisherman's Wharf": 13,
            "Bayview": 22,
            "Mission District": 15,
            "Alamo Square": 10,
            "Golden Gate Park": 15
        },
        "Mission District": {
            "Presidio": 25,
            "Marina District": 19,
            "The Castro": 7,
            "Fisherman's Wharf": 22,
            "Bayview": 14,
            "Pacific Heights": 16,
            "Alamo Square": 11,
            "Golden Gate Park": 17
        },
        "Alamo Square": {
            "Presidio": 17,
            "Marina District": 15,
            "The Castro": 8,
            "Fisherman's Wharf": 19,
            "Bayview": 16,
            "Pacific Heights": 10,
            "Mission District": 10,
            "Golden Gate Park": 9
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Marina District": 16,
            "The Castro": 13,
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Pacific Heights": 16,
            "Mission District": 17,
            "Alamo Square": 9
        }
    }

    # Helper function to convert time string to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Helper function to convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each friend's meeting start and end times
    meet_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meet_vars.append((friend, start, end))

    # Add constraints for each friend's meeting
    for friend, start, end in meet_vars:
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Meeting must start and end within the friend's availability
        s.add(start >= available_start)
        s.add(end <= available_end)
        # Meeting duration must be at least the minimum required
        s.add(end - start >= min_duration)
        # Start time must be before end time
        s.add(start < end)

    # Create variables to represent the order of meetings
    num_friends = len(friends)
    order = [Int(f"order_{i}") for i in range(num_friends)]
    # Each order variable must be between 0 and num_friends - 1
    for o in order:
        s.add(o >= 0)
        s.add(o < num_friends)
    # All order variables must be distinct
    s.add(Distinct(order))

    # Create variables to represent the current location at each step
    current_locations = [String(f"loc_{i}") for i in range(num_friends + 1)]
    # Initial location is Presidio
    s.add(current_locations[0] == "Presidio")

    # Create variables to represent the current time at each step
    current_times = [Int(f"time_{i}") for i in range(num_friends + 1)]
    # Initial time is 0 (9:00 AM)
    s.add(current_times[0] == 0)

    # Add constraints for the order of meetings
    for i in range(num_friends):
        # Get the friend index for the i-th meeting
        friend_idx = order[i]
        friend = friends[friend_idx]
        start = meet_vars[friend_idx][1]
        end = meet_vars[friend_idx][2]
        
        # The start time of the meeting must be after the current time plus travel time
        s.add(start >= current_times[i] + travel_times[current_locations[i]][friend["location"]])
        # Update current time and location
        s.add(current_times[i + 1] == end)
        s.add(current_locations[i + 1] == friend["location"])

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Get the actual order of meetings
        actual_order = sorted([(model[order[i]].as_long(), i) for i in range(num_friends)])
        itinerary = []
        
        for pos, i in actual_order:
            friend = friends[i]
            start = meet_vars[i][1]
            end = meet_vars[i][2]
            start_val = model[start].as_long()
            end_val = model[end].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
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