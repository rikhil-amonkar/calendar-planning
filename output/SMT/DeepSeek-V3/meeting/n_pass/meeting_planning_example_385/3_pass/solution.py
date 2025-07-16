from z3 import *
from itertools import permutations

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends data with their locations and availability windows
    friends = {
        'Jeffrey': {'location': 'Presidio', 'start': 8*60, 'end': 10*60, 'min_duration': 105},
        'Steven': {'location': 'North Beach', 'start': 13.5*60, 'end': 22*60, 'min_duration': 45},
        'Barbara': {'location': 'Fisherman\'s Wharf', 'start': 18*60, 'end': 21.5*60, 'min_duration': 30},
        'John': {'location': 'Pacific Heights', 'start': 9*60, 'end': 13.5*60, 'min_duration': 15}
    }

    # Travel times between locations in minutes
    travel_times = {
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Pacific Heights'): 11,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Pacific Heights'): 8,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13
    }

    # Create variables for meeting start and end times
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}')
        }

    # Current time and location
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Nob Hill'

    # Basic constraints for each meeting
    for name in friends:
        friend = friends[name]
        s.add(meeting_vars[name]['start'] >= friend['start'])
        s.add(meeting_vars[name]['end'] <= friend['end'])
        s.add(meeting_vars[name]['end'] - meeting_vars[name]['start'] >= friend['min_duration'])

    # Try all possible meeting orders
    for order in permutations(friends.keys()):
        temp_solver = Solver()
        temp_solver.add(s.assertions())

        # Add travel time constraints between meetings
        for i in range(len(order)-1):
            from_meeting = order[i]
            to_meeting = order[i+1]
            from_loc = friends[from_meeting]['location']
            to_loc = friends[to_meeting]['location']
            travel_time = travel_times[(from_loc, to_loc)]
            temp_solver.add(meeting_vars[to_meeting]['start'] >= meeting_vars[from_meeting]['end'] + travel_time)

        # Add constraint for first meeting
        first_meeting = order[0]
        first_loc = friends[first_meeting]['location']
        travel_time = travel_times[(current_location, first_loc)]
        temp_solver.add(meeting_vars[first_meeting]['start'] >= current_time + travel_time)

        if temp_solver.check() == sat:
            m = temp_solver.model()
            schedule = []
            for name in friends:
                start = m[meeting_vars[name]['start']].as_long()
                end = m[meeting_vars[name]['end']].as_long()
                schedule.append({
                    'friend': name,
                    'location': friends[name]['location'],
                    'start': f"{start//60}:{start%60:02d}",
                    'end': f"{end//60}:{end%60:02d}",
                    'duration': end - start
                })
            return schedule

    return None

# Solve and print the schedule
schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['friend']} at {meeting['location']} from {meeting['start']} to {meeting['end']} (duration: {meeting['duration']} minutes)")
else:
    print("No valid schedule found.")