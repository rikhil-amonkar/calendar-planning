from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations and friends
    friends = {
        'Jeffrey': {'location': 'Presidio', 'start': 8*60, 'end': 10*60, 'min_duration': 105},
        'Steven': {'location': 'North Beach', 'start': 13.5*60, 'end': 22*60, 'min_duration': 45},
        'Barbara': {'location': 'Fisherman\'s Wharf', 'start': 18*60, 'end': 21.5*60, 'min_duration': 30},
        'John': {'location': 'Pacific Heights', 'start': 9*60, 'end': 13.5*60, 'min_duration': 15}
    }

    # Travel times (in minutes) as a dictionary: (from, to) -> time
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

    # Variables for start and end times of each meeting
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Current location starts at Nob Hill at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Nob Hill'

    # Add constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(meeting_start[name] >= friend['start'])
        s.add(meeting_end[name] <= friend['end'])
        s.add(meeting_end[name] - meeting_start[name] >= friend['min_duration'])

    # Determine meeting order (try all permutations to find feasible schedule)
    from itertools import permutations
    for order in permutations(friends.keys()):
        temp_solver = Solver()
        temp_solver.add(s.assertions())

        # Enforce travel times between meetings
        for i in range(len(order) - 1):
            from_meeting = order[i]
            to_meeting = order[i + 1]
            from_loc = friends[from_meeting]['location']
            to_loc = friends[to_meeting]['location']
            travel_time = travel_times.get((from_loc, to_loc), 0)
            temp_solver.add(meeting_start[to_meeting] >= meeting_end[from_meeting] + travel_time)

        # First meeting must be after travel from Nob Hill
        first_meeting = order[0]
        first_loc = friends[first_meeting]['location']
        travel_time = travel_times.get((current_location, first_loc), 0)
        temp_solver.add(meeting_start[first_meeting] >= current_time + travel_time)

        if temp_solver.check() == sat:
            m = temp_solver.model()
            schedule = []
            for name in friends:
                start = m[meeting_start[name]].as_long()
                end = m[meeting_end[name]].as_long()
                schedule.append({
                    'friend': name,
                    'location': friends[name]['location'],
                    'start': f"{start // 60}:{start % 60:02d}",
                    'end': f"{end // 60}:{end % 60:02d}",
                    'duration': end - start
                })
            return schedule

    return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['friend']} at {meeting['location']} from {meeting['start']} to {meeting['end']} (duration: {meeting['duration']} minutes)")
else:
    print("No valid schedule found.")