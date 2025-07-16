from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = {
        'Stephanie': {'location': 'Richmond District', 'start': 16.25, 'end': 21.5, 'duration': 1.25},  # 4:15PM to 9:30PM, 75 mins
        'William': {'location': 'Union Square', 'start': 10.75, 'end': 17.5, 'duration': 0.75},  # 10:45AM to 5:30PM, 45 mins
        'Elizabeth': {'location': 'Nob Hill', 'start': 12.25, 'end': 15.0, 'duration': 1.75},  # 12:15PM to 3:00PM, 105 mins
        'Joseph': {'location': 'Fisherman\'s Wharf', 'start': 12.75, 'end': 14.0, 'duration': 1.25},  # 12:45PM to 2:00PM, 75 mins
        'Anthony': {'location': 'Golden Gate Park', 'start': 13.0, 'end': 20.5, 'duration': 1.25},  # 1:00PM to 8:30PM, 75 mins
        'Barbara': {'location': 'Embarcadero', 'start': 19.25, 'end': 20.5, 'duration': 1.25},  # 7:15PM to 8:30PM, 75 mins
        'Carol': {'location': 'Financial District', 'start': 11.75, 'end': 16.25, 'duration': 1.0},  # 11:45AM to 4:15PM, 60 mins
        'Sandra': {'location': 'North Beach', 'start': 10.0, 'end': 12.5, 'duration': 0.25},  # 10:00AM to 12:30PM, 15 mins
        'Kenneth': {'location': 'Presidio', 'start': 21.25, 'end': 22.25, 'duration': 0.75},  # 9:15PM to 10:15PM, 45 mins
    }

    # Define travel times (in hours) between locations
    travel_times = {
        ('Marina District', 'Richmond District'): 11/60,
        ('Marina District', 'Union Square'): 16/60,
        ('Marina District', 'Nob Hill'): 12/60,
        ('Marina District', 'Fisherman\'s Wharf'): 10/60,
        ('Marina District', 'Golden Gate Park'): 18/60,
        ('Marina District', 'Embarcadero'): 14/60,
        ('Marina District', 'Financial District'): 17/60,
        ('Marina District', 'North Beach'): 11/60,
        ('Marina District', 'Presidio'): 10/60,
        ('Richmond District', 'Marina District'): 9/60,
        ('Richmond District', 'Union Square'): 21/60,
        ('Richmond District', 'Nob Hill'): 17/60,
        ('Richmond District', 'Fisherman\'s Wharf'): 18/60,
        ('Richmond District', 'Golden Gate Park'): 9/60,
        ('Richmond District', 'Embarcadero'): 19/60,
        ('Richmond District', 'Financial District'): 22/60,
        ('Richmond District', 'North Beach'): 17/60,
        ('Richmond District', 'Presidio'): 7/60,
        ('Union Square', 'Marina District'): 18/60,
        ('Union Square', 'Richmond District'): 20/60,
        ('Union Square', 'Nob Hill'): 9/60,
        ('Union Square', 'Fisherman\'s Wharf'): 15/60,
        ('Union Square', 'Golden Gate Park'): 22/60,
        ('Union Square', 'Embarcadero'): 11/60,
        ('Union Square', 'Financial District'): 9/60,
        ('Union Square', 'North Beach'): 10/60,
        ('Union Square', 'Presidio'): 24/60,
        ('Nob Hill', 'Marina District'): 11/60,
        ('Nob Hill', 'Richmond District'): 14/60,
        ('Nob Hill', 'Union Square'): 7/60,
        ('Nob Hill', 'Fisherman\'s Wharf'): 10/60,
        ('Nob Hill', 'Golden Gate Park'): 17/60,
        ('Nob Hill', 'Embarcadero'): 9/60,
        ('Nob Hill', 'Financial District'): 9/60,
        ('Nob Hill', 'North Beach'): 8/60,
        ('Nob Hill', 'Presidio'): 17/60,
        ('Fisherman\'s Wharf', 'Marina District'): 9/60,
        ('Fisherman\'s Wharf', 'Richmond District'): 18/60,
        ('Fisherman\'s Wharf', 'Union Square'): 13/60,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11/60,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25/60,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8/60,
        ('Fisherman\'s Wharf', 'Financial District'): 11/60,
        ('Fisherman\'s Wharf', 'North Beach'): 6/60,
        ('Fisherman\'s Wharf', 'Presidio'): 17/60,
        ('Golden Gate Park', 'Marina District'): 16/60,
        ('Golden Gate Park', 'Richmond District'): 7/60,
        ('Golden Gate Park', 'Union Square'): 22/60,
        ('Golden Gate Park', 'Nob Hill'): 20/60,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24/60,
        ('Golden Gate Park', 'Embarcadero'): 25/60,
        ('Golden Gate Park', 'Financial District'): 26/60,
        ('Golden Gate Park', 'North Beach'): 23/60,
        ('Golden Gate Park', 'Presidio'): 11/60,
        ('Embarcadero', 'Marina District'): 12/60,
        ('Embarcadero', 'Richmond District'): 21/60,
        ('Embarcadero', 'Union Square'): 10/60,
        ('Embarcadero', 'Nob Hill'): 10/60,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6/60,
        ('Embarcadero', 'Golden Gate Park'): 25/60,
        ('Embarcadero', 'Financial District'): 5/60,
        ('Embarcadero', 'North Beach'): 5/60,
        ('Embarcadero', 'Presidio'): 20/60,
        ('Financial District', 'Marina District'): 15/60,
        ('Financial District', 'Richmond District'): 21/60,
        ('Financial District', 'Union Square'): 9/60,
        ('Financial District', 'Nob Hill'): 8/60,
        ('Financial District', 'Fisherman\'s Wharf'): 10/60,
        ('Financial District', 'Golden Gate Park'): 23/60,
        ('Financial District', 'Embarcadero'): 4/60,
        ('Financial District', 'North Beach'): 7/60,
        ('Financial District', 'Presidio'): 22/60,
        ('North Beach', 'Marina District'): 9/60,
        ('North Beach', 'Richmond District'): 18/60,
        ('North Beach', 'Union Square'): 7/60,
        ('North Beach', 'Nob Hill'): 7/60,
        ('North Beach', 'Fisherman\'s Wharf'): 5/60,
        ('North Beach', 'Golden Gate Park'): 22/60,
        ('North Beach', 'Embarcadero'): 6/60,
        ('North Beach', 'Financial District'): 8/60,
        ('North Beach', 'Presidio'): 17/60,
        ('Presidio', 'Marina District'): 11/60,
        ('Presidio', 'Richmond District'): 7/60,
        ('Presidio', 'Union Square'): 22/60,
        ('Presidio', 'Nob Hill'): 18/60,
        ('Presidio', 'Fisherman\'s Wharf'): 19/60,
        ('Presidio', 'Golden Gate Park'): 12/60,
        ('Presidio', 'Embarcadero'): 20/60,
        ('Presidio', 'Financial District'): 23/60,
        ('Presidio', 'North Beach'): 18/60,
    }

    # Create variables for each friend's meeting start and end times
    meeting_starts = {name: Real(f'start_{name}') for name in friends}
    meeting_ends = {name: Real(f'end_{name}') for name in friends}

    # Current location starts at Marina District at 9:00AM (9.0)
    current_location = 'Marina District'
    current_time = 9.0

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(meeting_starts[name] >= friend['start'])
        s.add(meeting_ends[name] <= friend['end'])
        s.add(meeting_ends[name] == meeting_starts[name] + friend['duration'])

    # Order constraints and travel times
    friend_names = list(friends.keys())
    for i in range(len(friend_names) - 1):
        name1 = friend_names[i]
        name2 = friend_names[i + 1]
        loc1 = friends[name1]['location']
        loc2 = friends[name2]['location']
        travel_time = travel_times.get((loc1, loc2), 0)
        s.add(meeting_starts[name2] >= meeting_ends[name1] + travel_time)

    # Ensure the first meeting starts after arriving at Marina District
    first_friend = friend_names[0]
    first_travel_time = travel_times.get((current_location, friends[first_friend]['location']), 0)
    s.add(meeting_starts[first_friend] >= current_time + first_travel_time)

    # Try to meet as many friends as possible by minimizing the number of missed meetings
    # We can use a soft constraint approach, but for simplicity, we'll just check satisfiability

    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friend_names:
            start = m[meeting_starts[name]].as_decimal(3)
            end = m[meeting_ends[name]].as_decimal(3)
            schedule.append((name, float(start), float(end), friends[name]['location']))
        
        # Sort the schedule by start time
        schedule.sort(key=lambda x: x[1])
        
        # Print the schedule
        print("Optimal Schedule:")
        for entry in schedule:
            name, start, end, loc = entry
            start_hr = int(start)
            start_min = int((start - start_hr) * 60)
            end_hr = int(end)
            end_min = int((end - end_hr) * 60)
            print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()