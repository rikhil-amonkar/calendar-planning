from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Define friends and their availability
    friends = {
        "Charles": {"location": "Presidio", "start": "13:15", "end": "15:00", "duration": 105},
        "Robert": {"location": "Nob Hill", "start": "13:15", "end": "17:30", "duration": 90},
        "Nancy": {"location": "Pacific Heights", "start": "14:45", "end": "22:00", "duration": 105},
        "Brian": {"location": "Mission District", "start": "15:30", "end": "22:00", "duration": 60},
        "Kimberly": {"location": "Marina District", "start": "17:00", "end": "19:45", "duration": 75},
        "David": {"location": "North Beach", "start": "14:45", "end": "16:30", "duration": 75},
        "William": {"location": "Russian Hill", "start": "12:30", "end": "19:15", "duration": 120},
        "Jeffrey": {"location": "Richmond District", "start": "12:00", "end": "19:15", "duration": 45},
        "Karen": {"location": "Embarcadero", "start": "14:15", "end": "20:45", "duration": 60},
        "Joshua": {"location": "Alamo Square", "start": "18:45", "end": "22:00", "duration": 60}
    }

    # Convert time strings to minutes since 0:00
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        duration = friend["duration"]
        
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        
        s.add(start_var >= start_min)
        s.add(end_var <= end_min)
        s.add(end_var == start_var + duration)
        
        friends[name]["start_var"] = start_var
        friends[name]["end_var"] = end_var

    # Define travel times
    travel_times = {
        "Sunset District": {
            "Presidio": 16, "Nob Hill": 27, "Pacific Heights": 21, "Mission District": 25,
            "Marina District": 21, "North Beach": 28, "Russian Hill": 24, "Richmond District": 12,
            "Embarcadero": 30, "Alamo Square": 17
        },
        "Presidio": {
            "Sunset District": 15, "Nob Hill": 18, "Pacific Heights": 11, "Mission District": 26,
            "Marina District": 11, "North Beach": 18, "Russian Hill": 14, "Richmond District": 7,
            "Embarcadero": 20, "Alamo Square": 19
        },
        "Nob Hill": {
            "Sunset District": 24, "Presidio": 17, "Pacific Heights": 8, "Mission District": 13,
            "Marina District": 11, "North Beach": 8, "Russian Hill": 5, "Richmond District": 14,
            "Embarcadero": 9, "Alamo Square": 11
        },
        "Pacific Heights": {
            "Sunset District": 21, "Presidio": 11, "Nob Hill": 8, "Mission District": 15,
            "Marina District": 6, "North Beach": 9, "Russian Hill": 7, "Richmond District": 12,
            "Embarcadero": 10, "Alamo Square": 10
        },
        "Mission District": {
            "Sunset District": 24, "Presidio": 25, "Nob Hill": 12, "Pacific Heights": 16,
            "Marina District": 19, "North Beach": 17, "Russian Hill": 15, "Richmond District": 20,
            "Embarcadero": 19, "Alamo Square": 11
        },
        "Marina District": {
            "Sunset District": 19, "Presidio": 10, "Nob Hill": 12, "Pacific Heights": 7,
            "Mission District": 20, "North Beach": 11, "Russian Hill": 8, "Richmond District": 11,
            "Embarcadero": 14, "Alamo Square": 15
        },
        "North Beach": {
            "Sunset District": 27, "Presidio": 17, "Nob Hill": 7, "Pacific Heights": 8,
            "Mission District": 18, "Marina District": 9, "Russian Hill": 4, "Richmond District": 18,
            "Embarcadero": 6, "Alamo Square": 16
        },
        "Russian Hill": {
            "Sunset District": 23, "Presidio": 14, "Nob Hill": 5, "Pacific Heights": 7,
            "Mission District": 16, "Marina District": 7, "North Beach": 5, "Richmond District": 14,
            "Embarcadero": 8, "Alamo Square": 15
        },
        "Richmond District": {
            "Sunset District": 11, "Presidio": 7, "Nob Hill": 17, "Pacific Heights": 10,
            "Mission District": 20, "Marina District": 9, "North Beach": 17, "Russian Hill": 13,
            "Embarcadero": 19, "Alamo Square": 13
        },
        "Embarcadero": {
            "Sunset District": 30, "Presidio": 20, "Nob Hill": 10, "Pacific Heights": 11,
            "Mission District": 20, "Marina District": 12, "North Beach": 5, "Russian Hill": 8,
            "Richmond District": 21, "Alamo Square": 19
        },
        "Alamo Square": {
            "Sunset District": 16, "Presidio": 17, "Nob Hill": 11, "Pacific Heights": 10,
            "Mission District": 10, "Marina District": 15, "North Beach": 15, "Russian Hill": 13,
            "Richmond District": 11, "Embarcadero": 16
        }
    }

    # Create a list of friend names
    friend_names = list(friends.keys())
    n = len(friend_names)

    # Create variables to represent whether we meet each friend
    meet = [Bool(f"meet_{name}") for name in friend_names]

    # Create variables for start and end times of each possible meeting
    start_times = [Int(f"start_{name}") for name in friend_names]
    end_times = [Int(f"end_{name}") for name in friend_names]

    # Create variables to represent the order of meetings
    # We'll use a simplified approach that doesn't require complex ordering constraints
    current_location = "Sunset District"
    current_time = 9 * 60  # Start at 9:00 AM

    itinerary = []

    # Try to meet friends in a reasonable order based on their availability
    # This is a heuristic approach since the full ordering problem is complex
    ordered_friends = sorted(friend_names, key=lambda x: time_to_minutes(friends[x]["start"]))

    for name in ordered_friends:
        friend = friends[name]
        start_var = friends[name]["start_var"]
        end_var = friends[name]["end_var"]
        
        # Travel time from current location to friend's location
        travel_time = travel_times[current_location][friend["location"]]
        
        # Constraint: friend's start time >= current_time + travel_time
        s.add(Implies(meet[friend_names.index(name)], start_var >= current_time + travel_time))
        
        # If we meet this friend, update current_time and current_location
        new_current_time = If(meet[friend_names.index(name)], end_var, current_time)
        new_current_location = If(meet[friend_names.index(name)], friend["location"], current_location)
        
        current_time = new_current_time
        current_location = new_current_location

    # We want to meet as many friends as possible
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(n)]))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Build the itinerary
        final_itinerary = []
        current_time = 9 * 60
        current_location = "Sunset District"
        
        # Sort friends by their actual meeting times in the model
        meeting_times = []
        for name in friend_names:
            if is_true(model.eval(meet[friend_names.index(name)])):
                start_time = model.eval(friends[name]["start_var"]).as_long()
                meeting_times.append((start_time, name))
        
        # Sort by start time
        meeting_times.sort()
        
        for start_time, name in meeting_times:
            friend = friends[name]
            travel_time = travel_times[current_location][friend["location"]]
            actual_start = max(start_time, current_time + travel_time)
            actual_end = actual_start + friend["duration"]
            
            # Ensure the meeting fits within the friend's availability
            actual_start = max(actual_start, time_to_minutes(friend["start"]))
            actual_end = actual_start + friend["duration"]
            actual_end = min(actual_end, time_to_minutes(friend["end"]))
            
            final_itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(actual_start),
                "end_time": minutes_to_time(actual_end)
            })
            
            current_time = actual_end
            current_location = friend["location"]
        
        return {"itinerary": final_itinerary}
    else:
        return {"itinerary": []}

# Call the function and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))