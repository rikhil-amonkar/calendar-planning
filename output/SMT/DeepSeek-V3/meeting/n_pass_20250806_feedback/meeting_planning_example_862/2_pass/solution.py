import json
from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    s = Optimize()

    # Define friends data with availability and minimum durations
    friends = {
        "Laura": {"location": "Alamo Square", "start": 870, "end": 975, "min_duration": 75},
        "Brian": {"location": "Presidio", "start": 615, "end": 1020, "min_duration": 30},
        "Karen": {"location": "Russian Hill", "start": 1080, "end": 1215, "min_duration": 90},
        "Stephanie": {"location": "North Beach", "start": 615, "end": 960, "min_duration": 75},
        "Helen": {"location": "Golden Gate Park", "start": 690, "end": 1305, "min_duration": 120},
        "Sandra": {"location": "Richmond District", "start": 480, "end": 915, "min_duration": 30},
        "Mary": {"location": "Embarcadero", "start": 1005, "end": 1125, "min_duration": 120},
        "Deborah": {"location": "Financial District", "start": 1140, "end": 1245, "min_duration": 105},
        "Elizabeth": {"location": "Marina District", "start": 510, "end": 795, "min_duration": 105}
    }

    # Travel times dictionary (from, to) -> minutes
    travel_times = {
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Marina District"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Marina District"): 16,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Marina District"): 9,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17,
    }

    # Create meeting variables
    meetings = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meetings[name] = {'start': start, 'end': end, 'loc': friends[name]['location']}
        
        # Add basic constraints
        s.add(start >= friends[name]['start'])
        s.add(end <= friends[name]['end'])
        s.add(end - start >= friends[name]['min_duration'])

    # Current state starts at Mission District at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = "Mission District"

    # Create a list to track meeting order
    meeting_order = []
    for name in friends:
        meeting_order.append(name)

    # Add constraints for travel times between meetings
    for i in range(len(meeting_order)-1):
        name1 = meeting_order[i]
        name2 = meeting_order[i+1]
        loc1 = meetings[name1]['loc']
        loc2 = meetings[name2]['loc']
        
        # Get travel time between locations
        travel_time = travel_times.get((loc1, loc2), 0)
        
        # Add constraint that next meeting starts after previous ends + travel time
        s.add(meetings[name2]['start'] >= meetings[name1]['end'] + travel_time)

    # Add constraint that first meeting starts after initial time + travel time
    first_meeting = meeting_order[0]
    travel_time = travel_times.get((current_loc, meetings[first_meeting]['loc']), 0)
    s.add(meetings[first_meeting]['start'] >= current_time + travel_time)

    # Try to maximize the number of meetings
    s.maximize(Sum([If(meetings[name]['end'] > 0, 1, 0) for name in friends]))

    # Convert minutes to time string
    def minutes_to_time(mins):
        return f"{mins//60:02d}:{mins%60:02d}"

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in meeting_order:
            start = m.eval(meetings[name]['start']).as_long()
            end = m.eval(meetings[name]['end']).as_long()
            if start > 0 and end > 0:  # Only include scheduled meetings
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))