from z3 import *
import json

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their travel times
    locations = ['North Beach', 'Pacific Heights', 'Chinatown', 'Union Square', 'Mission District', 'Golden Gate Park', 'Nob Hill']
    travel_times = {
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Nob Hill'): 7,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Nob Hill'): 8,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Nob Hill'): 9,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Nob Hill'): 12,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Golden Gate Park'): 17,
    }

    # Define the friends and their availability
    friends = {
        'James': {'location': 'Pacific Heights', 'start': 20*60, 'end': 22*60, 'duration': 120},
        'Robert': {'location': 'Chinatown', 'start': 12*60 + 15, 'end': 16*60 + 45, 'duration': 90},
        'Jeffrey': {'location': 'Union Square', 'start': 9*60 + 30, 'end': 15*60 + 30, 'duration': 120},
        'Carol': {'location': 'Mission District', 'start': 18*60 + 15, 'end': 21*60 + 15, 'duration': 15},
        'Mark': {'location': 'Golden Gate Park', 'start': 11*60 + 30, 'end': 17*60 + 45, 'duration': 15},
        'Sandra': {'location': 'Nob Hill', 'start': 8*60, 'end': 15*60 + 30, 'duration': 15},
    }

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for person in friends:
        start = Int(f'start_{person}')
        end = Int(f'end_{person}')
        meeting_vars[person] = {'start': start, 'end': end}
        # Constraints: start and end times must be within the friend's availability
        s.add(start >= friends[person]['start'])
        s.add(end <= friends[person]['end'])
        s.add(end == start + friends[person]['duration'])
        s.add(start >= 0)
        s.add(end <= 24*60)  # End of day

    # Current location starts at North Beach at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'North Beach'

    # Define the order of meetings (we'll try to meet all friends)
    people = list(friends.keys())

    # To model the order, we'll use a list of booleans indicating whether a meeting is scheduled
    scheduled = [Bool(f'scheduled_{person}') for person in people]

    # Ensure that at least some meetings are scheduled
    s.add(Or(*scheduled))

    # For each person, if scheduled, their meeting must fit into the itinerary
    for i, person in enumerate(people):
        # If scheduled, the meeting must start after the current time plus travel time
        s.add(Implies(scheduled[i], meeting_vars[person]['start'] >= current_time + travel_times[(current_location, friends[person]['location'])]))
        # Update current_time and current_location if scheduled
        current_time = If(scheduled[i], meeting_vars[person]['end'], current_time)
        current_location = If(scheduled[i], friends[person]['location'], current_location)

    # Try to maximize the number of meetings
    # We'll use a simple approach: prioritize longer meetings first
    # This is a heuristic; a more complex approach could use optimization
    s.push()
    s.check()
    model = s.model()

    # Extract the scheduled meetings
    itinerary = []
    for person in people:
        if is_true(model.eval(scheduled[people.index(person)])):
            start = model.eval(meeting_vars[person]['start']).as_long()
            end = model.eval(meeting_vars[person]['end']).as_long()
            start_time = f"{start // 60:02d}:{start % 60:02d}"
            end_time = f"{end // 60:02d}:{end % 60:02d}"
            itinerary.append({"action": "meet", "person": person, "start_time": start_time, "end_time": end_time})

    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))

    return {"itinerary": itinerary}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))