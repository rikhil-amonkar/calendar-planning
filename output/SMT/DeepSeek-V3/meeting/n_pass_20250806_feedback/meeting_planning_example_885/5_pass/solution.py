from z3 import *
import json
from itertools import combinations

def solve_scheduling():
    s = Optimize()

    # Define friends and their details
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

    # Travel times dictionary
    travel_times = {
        "Russian Hill": {
            "Marina District": 7, "Financial District": 11, "Alamo Square": 15,
            "Golden Gate Park": 21, "The Castro": 21, "Bayview": 23,
            "Sunset District": 23, "Haight-Ashbury": 17, "Nob Hill": 5
        },
        "Marina District": {
            "Russian Hill": 8, "Financial District": 17, "Alamo Square": 15,
            "Golden Gate Park": 18, "The Castro": 22, "Bayview": 27,
            "Sunset District": 19, "Haight-Ashbury": 16, "Nob Hill": 12
        },
        # ... (other locations' travel times as before)
    }

    # Helper functions for time conversion
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        active = Bool(f'active_{name}')  # Whether we meet this friend
        meeting_vars[name] = {'start': start, 'end': end, 'active': active}

        # Constrain meetings to be within friend's availability
        available_start = time_to_minutes(friends[name]["available_start"])
        available_end = time_to_minutes(friends[name]["available_end"])
        min_duration = friends[name]["min_duration"]
        
        s.add(Implies(active, start >= available_start))
        s.add(Implies(active, end <= available_end))
        s.add(Implies(active, end == start + min_duration))

    # Starting point
    current_time = 540  # 9:00 AM in minutes
    current_location = "Russian Hill"

    # Create a list to track meeting order
    meeting_order = []
    prev_end = current_time
    prev_location = current_location

    # For each friend, create constraints for possible meeting sequence
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
                
            # Get travel time between locations
            loc1 = friends[name1]["location"]
            loc2 = friends[name2]["location"]
            travel = travel_times[loc1][loc2]
            
            # If we meet name1 before name2, ensure enough time between
            s.add(Implies(And(meeting_vars[name1]['active'], meeting_vars[name2]['active'],
                           meeting_vars[name1]['end'] + travel > meeting_vars[name2]['start']),
                         meeting_vars[name1]['end'] + travel <= meeting_vars[name2]['start']))

    # Maximize the number of friends met
    total_met = Sum([If(meeting_vars[name]['active'], 1, 0) for name in friends])
    s.maximize(total_met)

    # Check if solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Collect all active meetings
        active_meetings = []
        for name in friends:
            if is_true(model[meeting_vars[name]['active']]):
                start_val = model[meeting_vars[name]['start']].as_long()
                end_val = model[meeting_vars[name]['end']].as_long()
                active_meetings.append({
                    "name": name,
                    "start": start_val,
                    "end": end_val,
                    "location": friends[name]["location"]
                })
        
        # Sort meetings by start time
        active_meetings.sort(key=lambda x: x['start'])
        
        # Build itinerary in chronological order
        for meeting in active_meetings:
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the schedule
solution = solve_scheduling()
print(json.dumps(solution, indent=2))