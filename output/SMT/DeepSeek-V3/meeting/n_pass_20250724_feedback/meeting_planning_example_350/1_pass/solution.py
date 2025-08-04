from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Financial District'): 13,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Financial District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Haight-Ashbury'): 19,
    }

    # Define friends' availability and meeting constraints
    friends = {
        'Mary': {
            'location': 'Pacific Heights',
            'start': 10 * 60,  # 10:00 AM in minutes
            'end': 19 * 60,    # 7:00 PM in minutes
            'duration': 45     # 45 minutes
        },
        'Lisa': {
            'location': 'Mission District',
            'start': 20 * 60 + 30,  # 8:30 PM in minutes
            'end': 22 * 60,         # 10:00 PM in minutes
            'duration': 75           # 75 minutes
        },
        'Betty': {
            'location': 'Haight-Ashbury',
            'start': 7 * 60 + 15,    # 7:15 AM in minutes
            'end': 17 * 60 + 15,     # 5:15 PM in minutes
            'duration': 90           # 90 minutes
        },
        'Charles': {
            'location': 'Financial District',
            'start': 11 * 60 + 15,   # 11:15 AM in minutes
            'end': 15 * 60,          # 3:00 PM in minutes
            'duration': 120          # 120 minutes
        }
    }

    # Current location and time
    current_location = 'Bayview'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Variables to track meetings
    meetings = []
    itinerary = []

    # For each friend, create variables for meeting start and end times
    for name, info in friends.items():
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        s.add(start >= info['start'])
        s.add(end <= info['end'])
        s.add(end == start + info['duration'])
        meetings.append((name, info['location'], start, end))

    # Add constraints for travel times between meetings
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                name_i, loc_i, start_i, end_i = meetings[i]
                name_j, loc_j, start_j, end_j = meetings[j]
                # Ensure that if meeting j is after meeting i, there's enough travel time
                s.add(Implies(start_j > end_i, start_j >= end_i + travel_times[(loc_i, loc_j)]))

    # Ensure that the first meeting is after current time plus travel time
    for name, loc, start, end in meetings:
        s.add(start >= current_time + travel_times[(current_location, loc)])

    # Maximize the number of friends met (all in this case)
    # Since all friends can be met, we don't need to optimize further

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        # Collect all meetings with their times
        itinerary = []
        for name, loc, start, end in meetings:
            start_val = m.evaluate(start).as_long()
            end_val = m.evaluate(end).as_long()
            # Convert minutes to HH:MM format
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
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))