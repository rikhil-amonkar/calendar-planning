from z3 import *

def solve_scheduling():
    s = Solver()

    # Friends' data
    friends = {
        'Linda': {'location': 'Marina District', 'start': 18*60, 'end': 22*60, 'duration': 30},
        'Kenneth': {'location': 'The Castro', 'start': 14*60 + 45, 'end': 16*60 + 15, 'duration': 30},
        'Kimberly': {'location': 'Richmond District', 'start': 14*60 + 15, 'end': 22*60, 'duration': 30},
        'Paul': {'location': 'Alamo Square', 'start': 21*60, 'end': 21*60 + 30, 'duration': 15},
        'Carol': {'location': 'Financial District', 'start': 10*60 + 15, 'end': 12*60, 'duration': 60},
        'Brian': {'location': 'Presidio', 'start': 10*60, 'end': 21*60 + 30, 'duration': 75},
        'Laura': {'location': 'Mission District', 'start': 16*60 + 15, 'end': 20*60 + 30, 'duration': 30},
        'Sandra': {'location': 'Nob Hill', 'start': 9*60 + 15, 'end': 18*60 + 30, 'duration': 60},
        'Karen': {'location': 'Russian Hill', 'start': 18*60 + 30, 'end': 22*60, 'duration': 75}
    }

    # Travel times (in minutes) between locations
    travel_times = {
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Russian Hill'): 8,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Financial District'): 21,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Russian Hill'): 18,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Russian Hill'): 13,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'The Castro'): 20,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Russian Hill'): 11,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Financial District'): 15,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Russian Hill'): 15,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Financial District'): 11,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Nob Hill'): 5
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}
        # Constraint: meeting duration
        s.add(end == start + friends[name]['duration'])
        # Constraint: meeting within friend's availability
        s.add(start >= friends[name]['start'])
        s.add(end <= friends[name]['end'])

    # Current location starts at Pacific Heights at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'Pacific Heights'

    # List to keep track of the order of meetings
    meeting_order = []

    # For each friend, determine if we can meet them considering travel time
    for name in friends:
        # Travel time from current_location to friend's location
        from_loc = current_location
        to_loc = friends[name]['location']
        travel_key = (from_loc, to_loc)
        if travel_key not in travel_times:
            # Try swapping the names if not found
            travel_key = (to_loc, from_loc)
            if travel_key not in travel_times:
                # Assume a default large travel time if not found
                travel_time = 60  # large penalty if not found
            else:
                travel_time = travel_times[travel_key]
        else:
            travel_time = travel_times[travel_key]

        # The meeting can only start after current_time + travel_time
        s.add(meeting_vars[name]['start'] >= current_time + travel_time)

        # After meeting, update current_time and current_location
        current_time = meeting_vars[name]['end']
        current_location = to_loc
        meeting_order.append(name)

    # Ensure no overlapping meetings (though the order enforces this)
    # Additional constraints can be added if needed

    # Try to meet all friends
    if s.check() == sat:
        model = s.model()
        schedule = []
        for name in friends:
            start_val = model[meeting_vars[name]['start']].as_long()
            end_val = model[meeting_vars[name]['end']].as_long()
            schedule.append((name, start_val, end_val))
        schedule.sort(key=lambda x: x[1])  # Sort by start time
        print("SOLUTION:")
        for name, start, end in schedule:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            print(f"Meet {name} at {friends[name]['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No feasible schedule found to meet all friends.")

solve_scheduling()