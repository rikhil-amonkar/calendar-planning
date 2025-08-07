from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their constraints
    friends = [
        {"name": "Linda", "location": "Marina District", "start": "18:00", "end": "22:00", "duration": 30},
        {"name": "Kenneth", "location": "The Castro", "start": "14:45", "end": "16:15", "duration": 30},
        {"name": "Kimberly", "location": "Richmond District", "start": "14:15", "end": "22:00", "duration": 30},
        {"name": "Paul", "location": "Alamo Square", "start": "21:00", "end": "21:30", "duration": 15},
        {"name": "Carol", "location": "Financial District", "start": "10:15", "end": "12:00", "duration": 60},
        {"name": "Brian", "location": "Presidio", "start": "10:00", "end": "21:30", "duration": 75},
        {"name": "Laura", "location": "Mission District", "start": "16:15", "end": "20:30", "duration": 30},
        {"name": "Sandra", "location": "Nob Hill", "start": "09:15", "end": "18:30", "duration": 60},
        {"name": "Karen", "location": "Russian Hill", "start": "18:30", "end": "22:00", "duration": 75}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times
    for friend in friends:
        friend['start_min'] = time_to_minutes(friend['start'])
        friend['end_min'] = time_to_minutes(friend['end'])
        friend['var_start'] = Int(f"start_{friend['name']}")
        friend['var_end'] = Int(f"end_{friend['name']}")
        # Constrain start and end times to be within the friend's window
        s.add(friend['var_start'] >= friend['start_min'])
        s.add(friend['var_end'] <= friend['end_min'])
        # Constrain duration
        s.add(friend['var_end'] - friend['var_start'] >= friend['duration'])

    # Define travel times (in minutes) between locations
    travel_times = {
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Russian Hill"): 8,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Russian Hill"): 13,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Russian Hill"): 11,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Russian Hill"): 15,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Nob Hill"): 5
    }

    # Define the order of meetings (this is a heuristic; in practice, we'd need to explore permutations)
    # For simplicity, we'll assume a specific order and check feasibility
    # Here, we'll try to schedule meetings in the order: Sandra, Carol, Brian, Kenneth, Laura, Kimberly, Linda, Karen, Paul
    # This is a heuristic and may not always work; a more robust approach would explore permutations or use optimization
    order = ["Sandra", "Carol", "Brian", "Kenneth", "Laura", "Kimberly", "Linda", "Karen", "Paul"]

    # Add constraints for travel times between consecutive meetings
    current_location = "Pacific Heights"
    current_time = 540  # 9:00 AM in minutes

    scheduled_meetings = []

    for i, name in enumerate(order):
        friend = next(f for f in friends if f['name'] == name)
        start_var = friend['var_start']
        end_var = friend['var_end']
        location = friend['location']
        
        # Travel time from current_location to friend's location
        travel_key = (current_location, location)
        travel_time = travel_times.get(travel_key, 0)  # Default to 0 if same location (shouldn't happen here)
        
        # Constraint: start_var >= current_time + travel_time
        s.add(start_var >= current_time + travel_time)
        
        # Update current_time and current_location
        scheduled_meetings.append((friend, start_var, end_var))
        current_time = end_var
        current_location = location

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend, start_var, end_var in scheduled_meetings:
            start = model.evaluate(start_var).as_long()
            end = model.evaluate(end_var).as_long()
            if start >= 0 and end >= 0 and end > start:
                itinerary.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))