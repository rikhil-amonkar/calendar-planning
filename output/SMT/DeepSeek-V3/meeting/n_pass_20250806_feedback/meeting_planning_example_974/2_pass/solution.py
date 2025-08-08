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

    # Create variables to represent the order of meetings
    friend_names = list(friends.keys())
    n = len(friend_names)
    order = [Int(f"order_{i}") for i in range(n)]
    
    # Each order variable must be between 0 and n-1
    for o in order:
        s.add(o >= 0, o < n)
    
    # All order variables must be distinct
    s.add(Distinct(order))
    
    # Create variables for the start time of each meeting in the sequence
    seq_start = [Int(f"seq_start_{i}") for i in range(n)]
    seq_end = [Int(f"seq_end_{i}") for i in range(n)]
    seq_location = [None] * n
    
    # Initial constraints
    current_time = 9 * 60  # Start at 9:00 AM
    current_location = "Sunset District"
    
    for i in range(n):
        # The i-th meeting is friends[friend_names[order[i]]]
        friend_idx = order[i]
        friend_name = friend_names[friend_idx]
        friend = friends[friend_name]
        
        # The meeting must start after current_time + travel time
        travel_time = travel_times[current_location][friend["location"]]
        s.add(seq_start[i] >= current_time + travel_time)
        
        # The meeting must be within the friend's availability
        s.add(seq_start[i] >= time_to_minutes(friend["start"]))
        s.add(seq_end[i] <= time_to_minutes(friend["end"]))
        s.add(seq_end[i] == seq_start[i] + friend["duration"])
        
        # Update current_time and current_location
        current_time = seq_end[i]
        current_location = friend["location"]
        seq_location[i] = friend["location"]
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Get the order of meetings
        meeting_order = [model.eval(o).as_long() for o in order]
        
        # Build the itinerary
        itinerary = []
        current_time = 9 * 60
        current_location = "Sunset District"
        
        for i in range(n):
            friend_idx = meeting_order[i]
            friend_name = friend_names[friend_idx]
            friend = friends[friend_name]
            
            travel_time = travel_times[current_location][friend["location"]]
            start_time = current_time + travel_time
            end_time = start_time + friend["duration"]
            
            # Ensure the meeting fits within the friend's availability
            start_time = max(start_time, time_to_minutes(friend["start"]))
            end_time = start_time + friend["duration"]
            end_time = min(end_time, time_to_minutes(friend["end"]))
            
            itinerary.append({
                "action": "meet",
                "person": friend_name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
            
            current_time = end_time
            current_location = friend["location"]
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Call the function and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))