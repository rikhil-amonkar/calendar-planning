import json
from z3 import *

def solve_scheduling_problem():
    # Initialize the optimization solver
    s = Optimize()

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Friends data with availability windows and minimum durations
    friends = {
        "Laura": {"location": "Alamo Square", "start": time_to_minutes("14:30"), "end": time_to_minutes("16:15"), "min_duration": 75},
        "Brian": {"location": "Presidio", "start": time_to_minutes("10:15"), "end": time_to_minutes("17:00"), "min_duration": 30},
        "Karen": {"location": "Russian Hill", "start": time_to_minutes("18:00"), "end": time_to_minutes("20:15"), "min_duration": 90},
        "Stephanie": {"location": "North Beach", "start": time_to_minutes("10:15"), "end": time_to_minutes("16:00"), "min_duration": 75},
        "Helen": {"location": "Golden Gate Park", "start": time_to_minutes("11:30"), "end": time_to_minutes("21:45"), "min_duration": 120},
        "Sandra": {"location": "Richmond District", "start": time_to_minutes("08:00"), "end": time_to_minutes("15:15"), "min_duration": 30},
        "Mary": {"location": "Embarcadero", "start": time_to_minutes("16:45"), "end": time_to_minutes("18:45"), "min_duration": 120},
        "Deborah": {"location": "Financial District", "start": time_to_minutes("19:00"), "end": time_to_minutes("20:45"), "min_duration": 105},
        "Elizabeth": {"location": "Marina District", "start": time_to_minutes("08:30"), "end": time_to_minutes("13:15"), "min_duration": 105}
    }

    # Travel times between locations (in minutes)
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
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Marina District"): 16,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Marina District"): 9,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        ("Financial District", "Marina District"): 15
    }

    # Create meeting variables
    meetings = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meetings[name] = {'start': start, 'end': end, 'loc': friends[name]['location']}
        
        # Basic meeting constraints
        s.add(start >= friends[name]['start'])
        s.add(end <= friends[name]['end'])
        s.add(end - start >= friends[name]['min_duration'])

    # Current state starts at Mission District at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = "Mission District"

    # Create a list of friend names
    friend_names = list(friends.keys())

    # Add travel time constraints between all possible meeting pairs
    for i in range(len(friend_names)):
        for j in range(len(friend_names)):
            if i == j:
                continue
                
            name1 = friend_names[i]
            name2 = friend_names[j]
            loc1 = meetings[name1]['loc']
            loc2 = meetings[name2]['loc']
            
            # Get travel time between locations (both directions)
            travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
            
            # Add constraint that if meeting2 is after meeting1, it must start after meeting1 ends + travel time
            s.add(Implies(
                meetings[name2]['start'] > meetings[name1]['start'],
                meetings[name2]['start'] >= meetings[name1]['end'] + travel_time
            ))

    # Add constraints for first meeting from starting location
    for name in friend_names:
        loc = meetings[name]['loc']
        travel_time = travel_times.get((current_loc, loc), 0)
        s.add(meetings[name]['start'] >= current_time + travel_time)

    # Maximize the number of meetings
    meeting_count = Int('meeting_count')
    s.add(meeting_count == Sum([If(meetings[name]['end'] > meetings[name]['start'], 1, 0) for name in friend_names]))
    s.maximize(meeting_count)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for name in friend_names:
            start = m.eval(meetings[name]['start']).as_long()
            end = m.eval(meetings[name]['end']).as_long()
            if start < end:  # Only include valid meetings
                scheduled_meetings.append({
                    "name": name,
                    "start": start,
                    "end": end
                })
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start'])
        
        # Build itinerary
        itinerary = []
        for meeting in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['end'])
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))