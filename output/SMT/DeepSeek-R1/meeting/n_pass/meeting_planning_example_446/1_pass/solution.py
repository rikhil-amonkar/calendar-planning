from z3 import *
import json

# Travel times dictionary
travel_times = {
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Union Square'): 21,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Chinatown'): 16,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Union Square'): 7,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Union Square'): 17,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Bayview'): 15
}

# Mapping of friends to locations
friend_to_location = {
    'Margaret': 'Bayview',
    'Kimberly': 'Marina District',
    'Robert': 'Chinatown',
    'Rebecca': 'Financial District',
    'Kenneth': 'Union Square'
}

# Minimum meeting durations in minutes
durations = {
    'Margaret': 30,
    'Kimberly': 15,
    'Robert': 15,
    'Rebecca': 75,
    'Kenneth': 75
}

# Time windows (start and end in minutes after 9:00 AM)
time_windows = {
    'Margaret': (30, 270),   # 9:30 AM to 1:30 PM (end inclusive: meeting must end by 1:30 PM)
    'Kimberly': (255, 465),  # 1:15 PM to 4:45 PM
    'Robert': (195, 675),    # 12:15 PM to 8:15 PM
    'Rebecca': (255, 465),   # 1:15 PM to 4:45 PM
    'Kenneth': (630, 735)    # 7:30 PM to 9:15 PM
}

friends = ['Margaret', 'Kimberly', 'Robert', 'Rebecca', 'Kenneth']

# Travel time from Richmond to each friend's location
T0 = [ travel_times[('Richmond District', friend_to_location[friend])] for friend in friends ]

# Duration array
d_array = [ durations[friend] for friend in friends ]

# Time window bounds: start_min and end_max for each meeting (end_max is the end of the window, so start + duration <= end_max)
low_bound = [ time_windows[friend][0] for friend in friends ]
high_bound_end = [ time_windows[friend][1] for friend in friends ]  # the meeting must end by this time
high_bound_start = [ high_bound_end[i] - d_array[i] for i in range(len(friends)) ]

# Create a list of locations for the friends
locs_list = [ friend_to_location[friend] for friend in friends ]

# Build the travel time matrix between the friends' locations (5x5)
T_matrix = []
for i in range(5):
    row = []
    for j in range(5):
        if i == j:
            row.append(0)
        else:
            from_loc = locs_list[i]
            to_loc = locs_list[j]
            row.append(travel_times[(from_loc, to_loc)])
    T_matrix.append(row)

# Create Z3 variables for start times
s0, s1, s2, s3, s4 = Ints('s0 s1 s2 s3 s4')
s_array = [s0, s1, s2, s3, s4]

# Create a variable for the minimum start time
min_start = Int('min_start')

solver = Solver()

# Constraints for time windows
for i in range(5):
    solver.add(s_array[i] >= low_bound[i])
    solver.add(s_array[i] <= high_bound_start[i])

# Constraint: min_start is the minimum of the start times
solver.add(min_start == Min(s_array))

# For the meeting that has the minimum start time, it must be >= travel time from Richmond
for i in range(5):
    solver.add(Implies(s_array[i] == min_start, min_start >= T0[i]))

# Pairwise constraints for every pair of meetings (i, j) with i < j
for i in range(5):
    for j in range(i+1, 5):
        # Either i comes before j or j comes before i
        before = s_array[i] + d_array[i] + T_matrix[i][j] <= s_array[j]
        after = s_array[j] + d_array[j] + T_matrix[j][i] <= s_array[i]
        solver.add(Or(before, after))

# Check if the problem is satisfiable
result = solver.check()
if result == sat:
    model = solver.model()
    # Extract the start times
    start_times = []
    for i in range(5):
        val = model.eval(s_array[i]).as_long()
        start_times.append(val)
    
    # Create list of meetings with start time, end time, and friend
    meetings = []
    for i in range(5):
        start_minutes = start_times[i]
        duration_minutes = d_array[i]
        end_minutes = start_minutes + duration_minutes
        # Convert to time string: start from 9:00 AM (0 minutes = 9:00 AM)
        total_minutes_from_9am = start_minutes
        hours = total_minutes_from_9am // 60
        minutes = total_minutes_from_9am % 60
        hour_start = 9 + hours
        minute_start = minutes
        start_time_str = f"{hour_start:02d}:{minute_start:02d}"
        
        total_minutes_end = end_minutes
        hours_end = total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        hour_end = 9 + hours_end
        minute_end = minutes_end
        end_time_str = f"{hour_end:02d}:{minute_end:02d}"
        
        meetings.append({
            "friend": friends[i],
            "start": start_minutes,
            "start_str": start_time_str,
            "end_str": end_time_str
        })
    
    # Sort meetings by start time
    meetings_sorted = sorted(meetings, key=lambda x: x['start'])
    
    # Build the itinerary in the required format
    itinerary = []
    for meet in meetings_sorted:
        itinerary.append({
            "action": "meet",
            "person": meet['friend'],
            "start_time": meet['start_str'],
            "end_time": meet['end_str']
        })
    
    # Output as JSON
    result_json = {"itinerary": itinerary}
    print(json.dumps(result_json, indent=2))
else:
    # If not satisfiable, we try to schedule a subset (not implemented here for brevity)
    print('No solution found for all five meetings. Trying with subsets is needed.')