from z3 import *

# Define the friends' data
friends_data = [
    {
        'name': 'Betty',
        'location': 'Russian Hill',
        'available_start': 7 * 60 + 0,  # 7:00 AM
        'available_end': 16 * 60 + 45,   # 4:45 PM
        'required_duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'Alamo Square',
        'available_start': 9 * 60 + 30,  # 9:30 AM
        'available_end': 17 * 60 + 15,   # 5:15 PM
        'required_duration': 105
    },
    {
        'name': 'Joshua',
        'location': 'Haight-Ashbury',
        'available_start': 12 * 60 + 15, # 12:15 PM
        'available_end': 19 * 60 + 0,    # 7:00 PM
        'required_duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Marina District',
        'available_start': 12 * 60 + 15, # 12:15 PM
        'available_end': 18 * 60 + 0,    # 6:00 PM
        'required_duration': 45
    },
    {
        'name': 'James',
        'location': 'Bayview',
        'available_start': 7 * 60 + 30,  # 7:30 AM
        'available_end': 20 * 60 + 0,    # 8:00 PM
        'required_duration': 90
    },
    {
        'name': 'Anthony',
        'location': 'Chinatown',
        'available_start': 11 * 60 + 45, # 11:45 AM
        'available_end': 13 * 60 + 30,   # 1:30 PM
        'required_duration': 75
    },
    {
        'name': 'Timothy',
        'location': 'Presidio',
        'available_start': 12 * 60 + 30, # 12:30 PM
        'available_end': 14 * 60 + 45,   # 2:45 PM
        'required_duration': 90
    },
    {
        'name': 'Emily',
        'location': 'Sunset District',
        'available_start': 19 * 60 + 30, # 7:30 PM
        'available_end': 21 * 60 + 30,   # 9:30 PM
        'required_duration': 120
    }
]

# Define locations and their indices
locations = [
    'Union Square',
    'Russian Hill',
    'Alamo Square',
    'Haight-Ashbury',
    'Marina District',
    'Bayview',
    'Chinatown',
    'Presidio',
    'Sunset District'
]

# Define travel_time matrix
travel_time = [
    # From Union Square
    [0, 13, 15, 18, 18, 15, 7, 24, 27],
    # From Russian Hill
    [10, 0, 15, 17, 7, 23, 9, 14, 23],
    # From Alamo Square
    [14, 13, 0, 5, 15, 16, 15, 17, 16],
    # From Haight-Ashbury
    [19, 17, 5, 0, 17, 18, 19, 15, 15],
    # From Marina District
    [16, 8, 15, 16, 0, 27, 15, 10, 19],
    # From Bayview
    [18, 23, 16, 19, 27, 0, 19, 32, 23],
    # From Chinatown
    [7, 7, 17, 19, 12, 19, 0, 19, 29],
    # From Presidio
    [22, 14, 19, 15, 11, 31, 21, 0, 16],
    # From Sunset District
    [30, 24, 17, 15, 21, 22, 30, 16, 0]
]

# Map each friend to their location index
friend_to_location = [1, 2, 3, 4, 5, 6, 7, 8]

# Create Z3 solver
s = Optimize()

# Create variables for the sequence of friends and their start times
friends = [Int(f'friend_{i}') for i in range(8)]
starts = [Int(f'start_{i}') for i in range(8)]

# Declare travel time function
travel_time_func = Function('travel_time_func', IntSort(), IntSort(), IntSort())

# Add constraints for the travel_time function
for i in range(9):
    for j in range(9):
        s.add(travel_time_func(i, j) == travel_time[i][j])

# Add constraints that all friends in the sequence are unique and within 0-7
for i in range(8):
    s.add(And(friends[i] >= 0, friends[i] <= 7))
for i in range(8):
    for j in range(i + 1, 8):
        s.add(friends[i] != friends[j])

# Add constraints for each friend in the sequence
for i in range(8):
    friend_i = friends[i]
    
    # Define available_start, available_end, duration, and loc for friend_i
    available_start_expr = If(friend_i == 0, 420,
        If(friend_i == 1, 570,
            If(friend_i == 2, 735,
                If(friend_i == 3, 735,
                    If(friend_i == 4, 450,
                        If(friend_i == 5, 705,
                            If(friend_i == 6, 750,
                                If(friend_i == 7, 1170, 0)))))))
    available_end_expr = If(friend_i == 0, 1005,
        If(friend_i == 1, 1035,
            If(friend_i == 2, 1140,
                If(friend_i == 3, 1080,
                    If(friend_i == 4, 1200,
                        If(friend_i == 5, 810,
                            If(friend_i == 6, 885,
                                If(friend_i == 7, 1290, 0)))))))
    duration_expr = If(friend_i == 0, 105,
        If(friend_i == 1, 105,
            If(friend_i == 2, 90,
                If(friend_i == 3, 45,
                    If(friend_i == 4, 90,
                        If(friend_i == 5, 75,
                            If(friend_i == 6, 90,
                                If(friend_i == 7, 120, 0)))))))
    loc_expr = If(friend_i == 0, 1,
        If(friend_i == 1, 2,
            If(friend_i == 2, 3,
                If(friend_i == 3, 4,
                    If(friend_i == 4, 5,
                        If(friend_i == 5, 6,
                            If(friend_i == 6, 7,
                                If(friend_i == 7, 8, 0)))))))
    
    # Add constraints for availability
    s.add(starts[i] >= available_start_expr)
    s.add(starts[i] + duration_expr <= available_end_expr)
    
    # Constraint for arrival time
    if i == 0:
        s.add(starts[i] >= 540 + travel_time_func(0, loc_expr))
    else:
        prev_friend_i = friends[i-1]
        prev_loc_expr = If(prev_friend_i == 0, 1,
            If(prev_friend_i == 1, 2,
                If(prev_friend_i == 2, 3,
                    If(prev_friend_i == 3, 4,
                        If(prev_friend_i == 4, 5,
                            If(prev_friend_i == 5, 6,
                                If(prev_friend_i == 6, 7,
                                    If(prev_friend_i == 7, 8, 0)))))))
        prev_duration_expr = If(prev_friend_i == 0, 105,
            If(prev_friend_i == 1, 105,
                If(prev_friend_i == 2, 90,
                    If(prev_friend_i == 3, 45,
                        If(prev_friend_i == 4, 90,
                            If(prev_friend_i == 5, 75,
                                If(prev_friend_i == 6, 90,
                                    If(prev_friend_i == 7, 120, 0)))))))
        travel_time_prev_to_current = travel_time_func(prev_loc_expr, loc_expr)
        s.add(starts[i] >= starts[i-1] + prev_duration_expr + travel_time_prev_to_current)

# Maximize the number of friends in the sequence
# Since all friends are unique and in 0-7, the count is 8 if all are included
s.maximize(8)

if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(8):
        friend_val = m.eval(friends[i]).as_long()
        if friend_val >= 0 and friend_val <= 7:
            start_val = m.eval(starts[i]).as_long()
            end_val = start_val + friends_data[friend_val]['required_duration']
            name = friends_data[friend_val]['name']
            loc = friends_data[friend_val]['location']
            def to_time(mins):
                hours = mins // 60
                minutes = mins % 60
                return f"{hours}:{minutes:02d}"
            start_time_str = to_time(start_val)
            end_time_str = to_time(end_val)
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")