from z3 import *
from itertools import permutations

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends data with locations and availability
    friends = {
        'Jeffrey': {'location': 'Presidio', 'start': 8*60, 'end': 10*60, 'min_duration': 105},
        'Steven': {'location': 'North Beach', 'start': 13.5*60, 'end': 22*60, 'min_duration': 45},
        'Barbara': {'location': 'Fisherman\'s Wharf', 'start': 18*60, 'end': 21.5*60, 'min_duration': 30},
        'John': {'location': 'Pacific Heights', 'start': 9*60, 'end': 13.5*60, 'min_duration': 15}
    }

    # Travel times between locations (in minutes)
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

    # Create meeting time variables
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Base constraints for each meeting
    for name in friends:
        s.add(meeting_start[name] >= friends[name]['start'])
        s.add(meeting_end[name] <= friends[name]['end'])
        s.add(meeting_end[name] - meeting_start[name] >= friends[name]['min_duration'])

    # Current state
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Nob Hill'

    # Try all possible meeting orders
    for order in permutations(friends.keys()):
        temp_s = Solver()
        temp_s.add(s.assertions())

        # Add travel constraints between meetings
        for i in range(len(order)-1):
            from_meet = order[i]
            to_meet = order[i+1]
            from_loc = friends[from_meet]['location']
            to_loc = friends[to_meet]['location']
            travel = travel_times[(from_loc, to_loc)]
            temp_s.add(meeting_start[to_meet] >= meeting_end[from_meet] + travel)

        # First meeting constraint
        first_meet = order[0]
        first_loc = friends[first_meet]['location']
        first_travel = travel_times[(current_location, first_loc)]
        temp_s.add(meeting_start[first_meet] >= current_time + first_travel)

        if temp_s.check() == sat:
            m = temp_s.model()
            schedule = []
            valid = True
            for name in friends:
                try:
                    start = m[meeting_start[name]].as_long()
                    end = m[meeting_end[name]].as_long()
                    if start > end:
                        valid = False
                        break
                    schedule.append({
                        'friend': name,
                        'location': friends[name]['location'],
                        'start': f"{start//60}:{start%60:02d}",
                        'end': f"{end//60}:{end%60:02d}",
                        'duration': end - start
                    })
                except:
                    valid = False
                    break
            
            if valid and len(schedule) == len(friends):
                return sorted(schedule, key=lambda x: x['start'])

    return None

# Execute and print results
schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['friend']} at {meeting['location']} from {meeting['start']} to {meeting['end']} (duration: {meeting['duration']} minutes)")
else:
    print("No valid schedule found.")