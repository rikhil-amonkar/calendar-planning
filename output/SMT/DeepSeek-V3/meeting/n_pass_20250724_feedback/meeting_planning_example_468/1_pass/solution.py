from z3 import *
import json

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the travel times between locations (in minutes)
    travel_times = {
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Bayview', 'The Castro'): 20,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    }

    # Define the friends and their availability
    friends = {
        'Rebecca': {
            'location': 'Bayview',
            'start_time': 9 * 60,  # 9:00 AM in minutes
            'end_time': 12 * 60 + 45,  # 12:45 PM in minutes
            'duration': 90,  # 90 minutes
        },
        'Amanda': {
            'location': 'Pacific Heights',
            'start_time': 18 * 60 + 30,  # 6:30 PM in minutes
            'end_time': 21 * 60 + 45,  # 9:45 PM in minutes
            'duration': 90,
        },
        'James': {
            'location': 'Alamo Square',
            'start_time': 9 * 60 + 45,  # 9:45 AM in minutes
            'end_time': 21 * 60 + 15,  # 9:15 PM in minutes
            'duration': 90,
        },
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'start_time': 8 * 60,  # 8:00 AM in minutes
            'end_time': 21 * 60 + 30,  # 9:30 PM in minutes
            'duration': 90,
        },
        'Melissa': {
            'location': 'Golden Gate Park',
            'start_time': 9 * 60,  # 9:00 AM in minutes
            'end_time': 18 * 60 + 45,  # 6:45 PM in minutes
            'duration': 90,
        }
    }

    # Create variables for each meeting's start and end times
    meetings = {}
    for name in friends:
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'duration': friends[name]['duration'],
            'location': friends[name]['location'],
            'available_start': friends[name]['start_time'],
            'available_end': friends[name]['end_time'],
        }

    # Add constraints for each meeting
    for name in meetings:
        m = meetings[name]
        s.add(m['start'] >= m['available_start'])
        s.add(m['end'] <= m['available_end'])
        s.add(m['end'] == m['start'] + m['duration'])

    # Add constraints to ensure no overlapping meetings and travel time between meetings
    names = list(meetings.keys())
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            m1 = meetings[names[i]]
            m2 = meetings[names[j]]
            # Either m1 is before m2 or m2 is before m1, with travel time
            travel = travel_times.get((m1['location'], m2['location']), 0)
            s.add(Or(
                m1['end'] + travel <= m2['start'],
                m2['end'] + travel_times.get((m2['location'], m1['location']), 0) <= m1['start']
            ))

    # Start at The Castro at 9:00 AM
    first_meeting = None
    for name in meetings:
        m = meetings[name]
        if first_meeting is None:
            first_meeting = m
            # The first meeting must start after traveling from The Castro
            s.add(m['start'] >= 9 * 60 + travel_times.get(('The Castro', m['location']), 0))
        else:
            pass

    # Try to maximize the number of meetings
    # We can do this by adding a constraint that all meetings must be scheduled
    # (since the problem asks to meet as many friends as possible)
    # Alternatively, we can prioritize certain friends if not all can be met

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in meetings:
            m = meetings[name]
            start = model.evaluate(m['start']).as_long()
            end = model.evaluate(m['end']).as_long()
            if start >= 0 and end >= 0:
                start_h = start // 60
                start_m = start % 60
                end_h = end // 60
                end_m = end % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_h:02d}:{start_m:02d}",
                    "end_time": f"{end_h:02d}:{end_m:02d}"
                })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))