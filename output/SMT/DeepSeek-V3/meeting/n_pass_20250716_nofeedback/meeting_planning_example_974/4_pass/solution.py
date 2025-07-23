from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define friends and their details
    friends = {
        "Charles": {"location": "Presidio", "start": "13:15", "end": "15:00", "min_duration": 105},
        "Robert": {"location": "Nob Hill", "start": "13:15", "end": "17:30", "min_duration": 90},
        "Nancy": {"location": "Pacific Heights", "start": "14:45", "end": "22:00", "min_duration": 105},
        "Brian": {"location": "Mission District", "start": "15:30", "end": "22:00", "min_duration": 60},
        "Kimberly": {"location": "Marina District", "start": "17:00", "end": "19:45", "min_duration": 75},
        "David": {"location": "North Beach", "start": "14:45", "end": "16:30", "min_duration": 75},
        "William": {"location": "Russian Hill", "start": "12:30", "end": "19:15", "min_duration": 120},
        "Jeffrey": {"location": "Richmond District", "start": "12:00", "end": "19:15", "min_duration": 45},
        "Karen": {"location": "Embarcadero", "start": "14:15", "end": "20:45", "min_duration": 60},
        "Joshua": {"location": "Alamo Square", "start": "18:45", "end": "22:00", "min_duration": 60}
    }

    # Travel times dictionary
    travel_times = {
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Alamo Square"): 15,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Alamo Square"): 15,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Alamo Square"): 13,
        ("Embarcadero", "Alamo Square"): 16
    }

    # Helper function to convert time string to minutes
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert friend availability to minutes
    for name in friends:
        friends[name]["start_min"] = time_to_minutes(friends[name]["start"])
        friends[name]["end_min"] = time_to_minutes(friends[name]["end"])
        friends[name]["min_duration_min"] = friends[name]["min_duration"]

    # Create Z3 variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = {
            'start': start_var,
            'end': end_var,
            'location': friends[name]["location"]
        }
        # Add constraints for meeting duration and availability
        s.add(start_var >= friends[name]["start_min"])
        s.add(end_var <= friends[name]["end_min"])
        s.add(end_var - start_var >= friends[name]["min_duration_min"])

    # Current location starts at Sunset District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Sunset District"

    # Define the order of meetings (prioritizing friends with tighter time windows)
    meeting_order = ["Jeffrey", "William", "Charles", "Robert", "David", "Karen", "Nancy", "Brian", "Kimberly", "Joshua"]

    # Add constraints for travel time between meetings
    prev_end = current_time
    prev_loc = current_location
    for name in meeting_order:
        if name in meeting_vars:
            travel_key = (prev_loc, friends[name]["location"])
            if travel_key in travel_times:
                travel_time = travel_times[travel_key]
            else:
                # Assume symmetric travel times or find reverse
                reverse_key = (friends[name]["location"], prev_loc)
                if reverse_key in travel_times:
                    travel_time = travel_times[reverse_key]
                else:
                    travel_time = 0  # Default, though this may not be realistic
            s.add(meeting_vars[name]['start'] >= prev_end + travel_time)
            prev_end = meeting_vars[name]['end']
            prev_loc = friends[name]["location"]

    # Add soft constraints to allow some flexibility in meeting durations
    for name in meeting_vars:
        duration = meeting_vars[name]['end'] - meeting_vars[name]['start']
        s.add_soft(duration >= friends[name]["min_duration_min"])

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in meeting_order:
            if name in meeting_vars:
                start_val = m[meeting_vars[name]['start']].as_long()
                end_val = m[meeting_vars[name]['end']].as_long()
                start_hh = start_val // 60
                start_mm = start_val % 60
                end_hh = end_val // 60
                end_mm = end_val % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))