from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their locations
    friends = {
        'Charles': 'Presidio',
        'Robert': 'Nob Hill',
        'Nancy': 'Pacific Heights',
        'Brian': 'Mission District',
        'Kimberly': 'Marina District',
        'David': 'North Beach',
        'William': 'Russian Hill',
        'Jeffrey': 'Richmond District',
        'Karen': 'Embarcadero',
        'Joshua': 'Alamo Square'
    }

    # Define the time slots for each friend
    time_slots = {
        'Charles': (13*60 + 15, 15*60),
        'Robert': (13*60 + 15, 17*60 + 30),
        'Nancy': (14*60 + 45, 22*60),
        'Brian': (15*60 + 30, 22*60),
        'Kimberly': (17*60, 19*60 + 45),
        'David': (14*60 + 45, 16*60 + 30),
        'William': (12*60 + 30, 19*60 + 15),
        'Jeffrey': (12*60, 19*60 + 15),
        'Karen': (14*60 + 15, 20*60 + 45),
        'Joshua': (18*60 + 45, 22*60)
    }

    # Minimum meeting durations in minutes
    min_durations = {
        'Charles': 105,
        'Robert': 90,
        'Nancy': 105,
        'Brian': 60,
        'Kimberly': 75,
        'David': 75,
        'William': 120,
        'Jeffrey': 45,
        'Karen': 60,
        'Joshua': 60
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Mission District'): 25,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Alamo Square'): 19,
        ('Nob Hill', 'Sunset District'): 24,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Alamo Square'): 11,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Alamo Square'): 15,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Alamo Square'): 13,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Embarcadero'): 16
    }

    # Create variables for start and end times of each meeting
    start_times = {friend: Int(f'start_{friend}') for friend in friends}
    end_times = {friend: Int(f'end_{friend}') for friend in friends}

    # Current location starts at Sunset District at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Sunset District'

    # To keep track of the order of meetings
    meeting_order = []

    # Add constraints for each friend
    for friend in friends:
        location = friends[friend]
        start_slot, end_slot = time_slots[friend]
        min_duration = min_durations[friend]

        # Meeting must start within the friend's time slot
        s.add(start_times[friend] >= start_slot)
        s.add(end_times[friend] <= end_slot)

        # Meeting duration must be at least the minimum required
        s.add(end_times[friend] - start_times[friend] >= min_duration)

        # Travel time from current location to friend's location
        travel_time = travel_times.get((current_location, location), 0)
        s.add(start_times[friend] >= current_time + travel_time)

        # Update current time and location after meeting
        current_time = end_times[friend]
        current_location = location
        meeting_order.append(friend)

    # Ensure no overlapping meetings (simplified by order)
    for i in range(len(meeting_order) - 1):
        friend1 = meeting_order[i]
        friend2 = meeting_order[i + 1]
        s.add(start_times[friend2] >= end_times[friend1] + travel_times.get((friends[friend1], friends[friend2]), 0)

    # Try to maximize the number of friends met
    # We can add a soft constraint or prioritize certain friends
    # For simplicity, we'll just check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        schedule = []
        for friend in friends:
            start = model.eval(start_times[friend]).as_long()
            end = model.eval(end_times[friend]).as_long()
            schedule.append((friend, friends[friend], start, end))
        
        # Sort schedule by start time
        schedule.sort(key=lambda x: x[2])
        
        # Print the schedule
        print("SOLUTION:")
        for entry in schedule:
            friend, location, start, end = entry
            start_hour = start // 60
            start_min = start % 60
            end_hour = end // 60
            end_min = end % 60
            print(f"Meet {friend} at {location} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()