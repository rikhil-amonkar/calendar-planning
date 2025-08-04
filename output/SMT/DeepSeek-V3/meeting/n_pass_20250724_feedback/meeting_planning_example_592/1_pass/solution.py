from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define locations and friends
    locations = ['North Beach', 'Pacific Heights', 'Chinatown', 'Union Square', 'Mission District', 'Golden Gate Park', 'Nob Hill']
    friends = {
        'James': {'location': 'Pacific Heights', 'start': 20*60, 'end': 22*60, 'min_duration': 120},
        'Robert': {'location': 'Chinatown', 'start': 12*60 + 15, 'end': 16*60 + 45, 'min_duration': 90},
        'Jeffrey': {'location': 'Union Square', 'start': 9*60 + 30, 'end': 15*60 + 30, 'min_duration': 120},
        'Carol': {'location': 'Mission District', 'start': 18*60 + 15, 'end': 21*60 + 15, 'min_duration': 15},
        'Mark': {'location': 'Golden Gate Park', 'start': 11*60 + 30, 'end': 17*60 + 45, 'min_duration': 15},
        'Sandra': {'location': 'Nob Hill', 'start': 8*60, 'end': 15*60 + 30, 'min_duration': 15}
    }

    # Travel times matrix (in minutes)
    travel_times = {
        'North Beach': {'Pacific Heights': 8, 'Chinatown': 6, 'Union Square': 7, 'Mission District': 18, 'Golden Gate Park': 22, 'Nob Hill': 7},
        'Pacific Heights': {'North Beach': 9, 'Chinatown': 11, 'Union Square': 12, 'Mission District': 15, 'Golden Gate Park': 15, 'Nob Hill': 8},
        'Chinatown': {'North Beach': 3, 'Pacific Heights': 10, 'Union Square': 7, 'Mission District': 18, 'Golden Gate Park': 23, 'Nob Hill': 8},
        'Union Square': {'North Beach': 10, 'Pacific Heights': 15, 'Chinatown': 7, 'Mission District': 14, 'Golden Gate Park': 22, 'Nob Hill': 9},
        'Mission District': {'North Beach': 17, 'Pacific Heights': 16, 'Chinatown': 16, 'Union Square': 15, 'Golden Gate Park': 17, 'Nob Hill': 12},
        'Golden Gate Park': {'North Beach': 24, 'Pacific Heights': 16, 'Chinatown': 23, 'Union Square': 22, 'Mission District': 17, 'Nob Hill': 20},
        'Nob Hill': {'North Beach': 8, 'Pacific Heights': 8, 'Chinatown': 6, 'Union Square': 7, 'Mission District': 13, 'Golden Gate Park': 17}
    }

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for friend in friends:
        start = Int(f'start_{friend}')
        end = Int(f'end_{friend}')
        meeting_vars[friend] = {'start': start, 'end': end}
        # Constrain meetings to be within the friend's availability
        s.add(start >= friends[friend]['start'])
        s.add(end <= friends[friend]['end'])
        s.add(end - start >= friends[friend]['min_duration'])
        s.add(start >= 0, end >= 0)

    # Current location starts at North Beach at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'North Beach'

    # Track the order of meetings
    meeting_order = []
    for friend in friends:
        meeting_order.append(friend)

    # Add constraints for travel time between meetings
    for i in range(len(meeting_order)):
        for j in range(i + 1, len(meeting_order)):
            friend1 = meeting_order[i]
            friend2 = meeting_order[j]
            loc1 = friends[friend1]['location']
            loc2 = friends[friend2]['location']
            travel_time = travel_times[loc1][loc2]

            # Ensure that the start time of friend2 is after the end time of friend1 plus travel time
            s.add(meeting_vars[friend2]['start'] >= meeting_vars[friend1]['end'] + travel_time)

    # Also ensure that the first meeting starts after travel time from North Beach
    for friend in friends:
        loc = friends[friend]['location']
        travel_time = travel_times[current_location][loc]
        s.add(meeting_vars[friend]['start'] >= current_time + travel_time)

    # Maximize the number of friends met (soft constraints)
    # We'll prioritize friends with longer required meeting times
    # For simplicity, we'll try to meet all friends and let Z3 handle infeasibility
    # If the problem is infeasible, we'll relax constraints one by one

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            start_val = model[meeting_vars[friend]['start']].as_long()
            end_val = model[meeting_vars[friend]['end']].as_long()
            start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
            itinerary.append({"action": "meet", "person": friend, "start_time": start_time, "end_time": end_time})
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem
result = solve_scheduling()
print(json.dumps(result, indent=2))