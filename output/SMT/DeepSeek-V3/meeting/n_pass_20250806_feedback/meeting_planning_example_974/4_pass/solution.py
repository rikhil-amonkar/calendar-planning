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

    # Create variables for travel times between consecutive meetings
    travel_time_vars = [Int(f"travel_{i}") for i in range(n)]

    # Create variables for the sequence of locations
    location_vars = [String(f"loc_{i}") for i in range(n+1)]
    s.add(location_vars[0] == "Sunset District")  # Starting location

    # Create variables for the sequence of times
    time_vars = [Int(f"time_{i}") for i in range(n+1)]
    s.add(time_vars[0] == 9 * 60)  # Start at 9:00 AM

    # Create variables for the order of meetings
    order = [Int(f"order_{i}") for i in range(n)]
    s.add([And(o >= 0, o < n) for o in order])
    s.add(Distinct(order))

    # Constraints for each meeting slot
    for i in range(n):
        # The friend being met in this slot
        friend_idx = order[i]
        friend_name = friend_names[friend_idx]
        friend = friends[friend_name]

        # If we meet this friend, their times must be valid
        s.add(Implies(meet[friend_idx],
                      And(time_vars[i+1] == time_vars[i] + travel_time_vars[i] + friend["duration"],
                          location_vars[i+1] == friend["location"],
                          time_vars[i] + travel_time_vars[i] >= time_to_minutes(friend["start"]),
                          time_vars[i] + travel_time_vars[i] + friend["duration"] <= time_to_minutes(friend["end"]))))

        # Travel time constraints
        for loc1 in travel_times:
            for loc2 in travel_times[loc1]:
                s.add(Implies(And(location_vars[i] == loc1, location_vars[i+1] == loc2),
                      travel_time_vars[i] == travel_times[loc1][loc2]))

    # We want to meet as many friends as possible
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(n)]))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Build the itinerary
        final_itinerary = []
        current_time = 9 * 60
        current_location = "Sunset District"

        # Get the meeting order from the model
        meeting_order = [model.eval(o).as_long() for o in order]
        
        for i in range(n):
            friend_idx = meeting_order[i]
            if is_true(model.eval(meet[friend_idx])):
                friend_name = friend_names[friend_idx]
                friend = friends[friend_name]
                
                # Get travel time
                travel_time = model.eval(travel_time_vars[i]).as_long()
                
                # Calculate meeting times
                start_time = current_time + travel_time
                end_time = start_time + friend["duration"]
                
                # Ensure within friend's availability
                start_time = max(start_time, time_to_minutes(friend["start"]))
                end_time = min(end_time, time_to_minutes(friend["end"]))
                
                final_itinerary.append({
                    "action": "meet",
                    "person": friend_name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                
                current_time = end_time
                current_location = friend["location"]
        
        return {"itinerary": final_itinerary}
    else:
        return {"itinerary": []}

# Call the function and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))