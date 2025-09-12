import json
from z3 import *

# Define travel times between locations
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

# Define friends' data
friends_data = {
    'James': {
        'location': 'Pacific Heights',
        'available_start': 20 * 60,  # 8:00 PM
        'available_end': 22 * 60,    # 10:00 PM
        'min_duration': 120
    },
    'Robert': {
        'location': 'Chinatown',
        'available_start': 12 * 60 + 15,  # 12:15 PM
        'available_end': 16 * 60 + 45,    # 4:45 PM
        'min_duration': 90
    },
    'Jeffrey': {
        'location': 'Union Square',
        'available_start': 9 * 60 + 30,  # 9:30 AM
        'available_end': 15 * 60 + 30,   # 3:30 PM
        'min_duration': 120
    },
    'Carol': {
        'location': 'Mission District',
        'available_start': 18 * 60 + 15,  # 6:15 PM
        'available_end': 21 * 60 + 15,    # 9:15 PM
        'min_duration': 15
    },
    'Mark': {
        'location': 'Golden Gate Park',
        'available_start': 11 * 60 + 30,  # 11:30 AM
        'available_end': 17 * 60 + 45,    # 5:45 PM
        'min_duration': 15
    },
    'Sandra': {
        'location': 'Nob Hill',
        'available_start': 8 * 60,  # 8:00 AM
        'available_end': 15 * 60 + 30,  # 3:30 PM
        'min_duration': 15
    }
}

friends_list = ['James', 'Robert', 'Jeffrey', 'Carol', 'Mark', 'Sandra']

# Create Z3 solver
solver = Solver()

# Create variables for each friend
meet_vars = {name: Bool(f'meet_{name}') for name in friends_list}
start_times = {name: Int(f'start_{name}') for name in friends_list}
end_times = {name: Int(f'end_{name}') for name in friends_list}

# Add constraints for each friend
for name in friends_list:
    data = friends_data[name]
    loc = data['location']
    available_start = data['available_start']
    available_end = data['available_end']
    min_duration = data['min_duration']
    
    # If the friend is met, their start time must be within available window, duration sufficient, and initial arrival time
    solver.add(If(meet_vars[name],
                  And(
                      start_times[name] >= available_start,
                      end_times[name] <= available_end,
                      end_times[name] - start_times[name] >= min_duration,
                      start_times[name] >= 9 * 60 + travel_times[('North Beach', loc)]
                  ),
                  True))

# Add pairwise constraints between all friends
for i in range(len(friends_list)):
    for j in range(i + 1, len(friends_list)):
        nameA = friends_list[i]
        nameB = friends_list[j]
        locA = friends_data[nameA]['location']
        locB = friends_data[nameB]['location']
        travel_time_A_to_B = travel_times[(locA, locB)]
        travel_time_B_to_A = travel_times[(locB, locA)]
        
        # If both are met, then their meetings must be ordered with sufficient travel time
        solver.add(Implies(
            And(meet_vars[nameA], meet_vars[nameB]),
            Or(
                start_times[nameB] >= end_times[nameA] + travel_time_A_to_B,
                start_times[nameA] >= end_times[nameB] + travel_time_B_to_A
            )
        ))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Collect the meetings that are met
    meetings = []
    for name in friends_list:
        if is_true(model.eval(meet_vars[name])):
            start = model.eval(start_times[name]).as_long()
            end = model.eval(end_times[name]).as_long()
            # Convert to H:MM format
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            meetings.append({
                "action": "meet",
                "location": friends_data[name]['location'],
                "person": name,
                "start_time": to_time_str(start),
                "end_time": to_time_str(end)
            })
    
    # Sort the meetings by start time to create itinerary
    meetings.sort(key=lambda x: x['start_time'])
    
    # Output as JSON
    print(json.dumps({"itinerary": meetings}, indent=2))
else:
    print("No solution found.")