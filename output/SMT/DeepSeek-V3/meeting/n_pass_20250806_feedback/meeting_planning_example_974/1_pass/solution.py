from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
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

    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
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
        
        # Real variables for start and end times in minutes since 9:00
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        
        # Constraints: start and end within availability window
        s.add(start_var >= start_min)
        s.add(end_var <= end_min)
        s.add(end_var == start_var + duration)
        s.add(start_var + duration <= end_min)
        
        friend["start_var"] = start_var
        friend["end_var"] = end_var

    # Define the order of meetings (permutation of friends)
    # We need to sequence the meetings with travel times
    # This is complex; instead, we can model the sequence as a list of booleans indicating whether a meeting is before another
    # But for simplicity, let's assume we can meet all friends and find a feasible order
    
    # Define travel times between locations
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

    # We need to sequence the meetings. Let's assume an arbitrary order and add constraints for travel times.
    # This is a simplified approach; a more comprehensive solution would involve permutation variables.
    # For this example, we'll try to meet friends in an order that minimizes conflicts.

    # Let's try to meet William first (earliest start time), then Jeffrey, then others.
    # Define a possible order: William, Jeffrey, Charles, Robert, David, Karen, Nancy, Brian, Kimberly, Joshua.
    ordered_friends = ["William", "Jeffrey", "Charles", "Robert", "David", "Karen", "Nancy", "Brian", "Kimberly", "Joshua"]
    # But let's adjust based on actual constraints.

    # Alternative approach: create a list of all friends and find a sequence that satisfies travel times.
    # This is complex; instead, we'll manually try to find a feasible sequence.

    # For the purpose of this example, let's assume the following sequence:
    sequence = ["Jeffrey", "William", "Charles", "Robert", "David", "Karen", "Nancy", "Brian", "Kimberly", "Joshua"]
    
    # For each consecutive pair in the sequence, add travel time constraints
    current_location = "Sunset District"
    current_time = 9 * 60  # 9:00 AM in minutes

    itinerary = []

    for name in sequence:
        friend = friends.get(name)
        if not friend:
            continue  # skip if not found (e.g., typo in name)
        
        start_var = friend["start_var"]
        end_var = friend["end_var"]
        location = friend["location"]
        
        # Travel time from current_location to friend's location
        travel_time = travel_times[current_location][location]
        
        # Constraint: friend's start time >= current_time + travel_time
        s.add(start_var >= current_time + travel_time)
        
        # Update current_time to friend's end time
        current_time = end_var
        current_location = location
        
        # Add to itinerary
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start_var),
            "end_time": minutes_to_time(end_var)
        })

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Update itinerary with actual times from the model
        final_itinerary = []
        for entry in itinerary:
            name = entry["person"]
            start_var = friends[name]["start_var"]
            end_var = friends[name]["end_var"]
            start_time = model.eval(start_var).as_long()
            end_time = model.eval(end_var).as_long()
            final_itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": final_itinerary}
    else:
        return {"itinerary": []}

# Call the function and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))