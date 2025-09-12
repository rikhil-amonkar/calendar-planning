from z3 import *
import json

# Travel times data
travel_time_data = [
    ("Union Square", "The Castro", 17),
    ("Union Square", "North Beach", 10),
    ("Union Square", "Embarcadero", 11),
    ("Union Square", "Alamo Square", 15),
    ("Union Square", "Nob Hill", 9),
    ("Union Square", "Presidio", 24),
    ("Union Square", "Fisherman's Wharf", 15),
    ("Union Square", "Mission District", 14),
    ("Union Square", "Haight-Ashbury", 18),
    ("The Castro", "Union Square", 19),
    ("The Castro", "North Beach", 20),
    ("The Castro", "Embarcadero", 22),
    ("The Castro", "Alamo Square", 8),
    ("The Castro", "Nob Hill", 16),
    ("The Castro", "Presidio", 20),
    ("The Castro", "Fisherman's Wharf", 24),
    ("The Castro", "Mission District", 7),
    ("The Castro", "Haight-Ashbury", 6),
    ("North Beach", "Union Square", 7),
    ("North Beach", "The Castro", 23),
    ("North Beach", "Embarcadero", 6),
    ("North Beach", "Alamo Square", 16),
    ("North Beach", "Nob Hill", 7),
    ("North Beach", "Presidio", 17),
    ("North Beach", "Fisherman's Wharf", 5),
    ("North Beach", "Mission District", 18),
    ("North Beach", "Haight-Ashbury", 18),
    ("Embarcadero", "Union Square", 10),
    ("Embarcadero", "The Castro", 25),
    ("Embarcadero", "North Beach", 5),
    ("Embarcadero", "Alamo Square", 19),
    ("Embarcadero", "Nob Hill", 10),
    ("Embarcadero", "Presidio", 20),
    ("Embarcadero", "Fisherman's Wharf", 6),
    ("Embarcadero", "Mission District", 20),
    ("Embarcadero", "Haight-Ashbury", 21),
    ("Alamo Square", "Union Square", 14),
    ("Alamo Square", "The Castro", 8),
    ("Alamo Square", "North Beach", 15),
    ("Alamo Square", "Embarcadero", 16),
    ("Alamo Square", "Nob Hill", 11),
    ("Alamo Square", "Presidio", 17),
    ("Alamo Square", "Fisherman's Wharf", 19),
    ("Alamo Square", "Mission District", 10),
    ("Alamo Square", "Haight-Ashbury", 5),
    ("Nob Hill", "Union Square", 7),
    ("Nob Hill", "The Castro", 17),
    ("Nob Hill", "North Beach", 8),
    ("Nob Hill", "Embarcadero", 9),
    ("Nob Hill", "Alamo Square", 11),
    ("Nob Hill", "Presidio", 17),
    ("Nob Hill", "Fisherman's Wharf", 10),
    ("Nob Hill", "Mission District", 13),
    ("Nob Hill", "Haight-Ashbury", 13),
    ("Presidio", "Union Square", 22),
    ("Presidio", "The Castro", 21),
    ("Presidio", "North Beach", 18),
    ("Presidio", "Embarcadero", 20),
    ("Presidio", "Alamo Square", 19),
    ("Presidio", "Nob Hill", 18),
    ("Presidio", "Fisherman's Wharf", 19),
    ("Presidio", "Mission District", 26),
    ("Presidio", "Haight-Ashbury", 15),
    ("Fisherman's Wharf", "Union Square", 13),
    ("Fisherman's Wharf", "The Castro", 27),
    ("Fisherman's Wharf", "North Beach", 6),
    ("Fisherman's Wharf", "Embarcadero", 8),
    ("Fisherman's Wharf", "Alamo Square", 21),
    ("Fisherman's Wharf", "Nob Hill", 11),
    ("Fisherman's Wharf", "Presidio", 17),
    ("Fisherman's Wharf", "Mission District", 22),
    ("Fisherman's Wharf", "Haight-Ashbury", 22),
    ("Mission District", "Union Square", 15),
    ("Mission District", "The Castro", 7),
    ("Mission District", "North Beach", 17),
    ("Mission District", "Embarcadero", 19),
    ("Mission District", "Alamo Square", 11),
    ("Mission District", "Nob Hill", 12),
    ("Mission District", "Presidio", 25),
    ("Mission District", "Fisherman's Wharf", 22),
    ("Mission District", "Haight-Ashbury", 12),
    ("Haight-Ashbury", "Union Square", 19),
    ("Haight-Ashbury", "The Castro", 6),
    ("Haight-Ashbury", "North Beach", 19),
    ("Haight-Ashbury", "Embarcadero", 20),
    ("Haight-Ashbury", "Alamo Square", 5),
    ("Haight-Ashbury", "Nob Hill", 15),
    ("Haight-Ashbury", "Presidio", 15),
    ("Haight-Ashbury", "Fisherman's Wharf", 23),
    ("Haight-Ashbury", "Mission District", 11),
]

# Build travel times dictionary
travel_times = {}
for from_loc, to_loc, time in travel_time_data:
    travel_times[(from_loc, to_loc)] = time

# Friends data
friends_data = [
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'available_start': 7 * 60,  # 7:00 AM
        'available_end': 10 * 60 + 30,  # 10:30 AM
        'min_duration': 15
    },
    {
        'name': 'Brian',
        'location': "Fisherman's Wharf",
        'available_start': 9 * 60 + 30,  # 9:30 AM
        'available_end': 15 * 60 + 30,  # 3:30 PM
        'min_duration': 45
    },
    {
        'name': 'Kenneth',
        'location': 'Nob Hill',
        'available_start': 12 * 60 + 15,  # 12:15 PM
        'available_end': 17 * 60 + 15,  # 5:15 PM
        'min_duration': 105
    },
    {
        'name': 'Joseph',
        'location': 'Embarcadero',
        'available_start': 15 * 60 + 30,  # 3:30 PM
        'available_end': 19 * 60 + 30,  # 7:30 PM
        'min_duration': 75
    },
    {
        'name': 'Joshua',
        'location': 'Presidio',
        'available_start': 16 * 60 + 30,  # 4:30 PM
        'available_end': 18 * 60 + 15,  # 6:15 PM
        'min_duration': 105
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'available_start': 20 * 60 + 45,  # 8:45 PM
        'available_end': 21 * 60 + 45,  # 9:45 PM
        'min_duration': 15
    },
    {
        'name': 'Steven',
        'location': 'Mission District',
        'available_start': 19 * 60,  # 7:00 PM
        'available_end': 21 * 60,  # 9:00 PM
        'min_duration': 90
    },
    {
        'name': 'Betty',
        'location': 'Haight-Ashbury',
        'available_start': 19 * 60,  # 7:00 PM
        'available_end': 20 * 60 + 30,  # 8:30 PM
        'min_duration': 90
    },
    {
        'name': 'Melissa',
        'location': 'The Castro',
        'available_start': 20 * 60 + 15,  # 8:15 PM
        'available_end': 21 * 60 + 15,  # 9:15 PM
        'min_duration': 30
    },
]

friends_locations = [
    'North Beach',  # Kimberly
    "Fisherman's Wharf",  # Brian
    'Nob Hill',  # Kenneth
    'Embarcadero',  # Joseph
    'Presidio',  # Joshua
    'Alamo Square',  # Barbara
    'Mission District',  # Steven
    'Haight-Ashbury',  # Betty
    'The Castro'  # Melissa
]

# Precompute friend_travel_times and union_to_friend_travel_times
friend_travel_times = [[0 for _ in range(9)] for _ in range(9)]
for i in range(9):
    for j in range(9):
        from_loc = friends_locations[i]
        to_loc = friends_locations[j]
        friend_travel_times[i][j] = travel_times[(from_loc, to_loc)]

union_to_friend_travel_times = []
for loc in friends_locations:
    union_to_friend_travel_times.append(travel_times[("Union Square", loc)])

# Z3 setup
opt = Optimize()

# Create variables for each position (0-8)
friends = [Int(f'friend_{i}') for i in range(9)]
starts = [Int(f'start_{i}') for i in range(9)]
ends = [Int(f'end_{i}') for i in range(9)]

# Add constraints that friends can be 0-8 or 9 (9 means no meeting)
for i in range(9):
    opt.add(And(friends[i] >= 0, friends[i] <= 9))

# Ensure each friend is scheduled at most once
for friend_index in range(9):
    opt.add(Sum([If(friends[i] == friend_index, 1, 0) for i in range(9)]) <= 1)

# For each position, add constraints for the meeting if included
for i in range(9):
    for friend_index in range(9):  # 0-8
        cond = And(friends[i] == friend_index, friends[i] != 9)
        friend_data = friends_data[friend_index]
        # start_i >= available_start
        opt.add(Implies(cond, starts[i] >= friend_data['available_start']))
        # end_i <= available_end
        opt.add(Implies(cond, ends[i] <= friend_data['available_end']))
        # end_i - start_i >= min_duration
        opt.add(Implies(cond, ends[i] - starts[i] >= friend_data['min_duration']))

# Add constraints for the first meeting's start time
for friend_index in range(9):
    cond = And(friends[0] == friend_index, friends[0] != 9)
    travel_time = union_to_friend_travel_times[friend_index]
    opt.add(Implies(cond, starts[0] >= 540 + travel_time))  # 540 is 9:00 AM

# Add constraints for consecutive meetings
for i in range(8):  # positions 0 to 7
    for prev in range(9):
        for curr in range(9):
            cond = And(friends[i] == prev, friends[i+1] == curr, prev != 9, curr != 9)
            travel_time = friend_travel_times[prev][curr]
            opt.add(Implies(cond, starts[i+1] >= ends[i] + travel_time))

# Objective: maximize the number of friends met
count = 0
for i in range(9):
    count += If(friends[i] != 9, 1, 0)
opt.maximize(count)

# Solve
result = opt.check()
if result == sat:
    model = opt.model()
    # Extract the solution
    itinerary = []
    for i in range(9):
        friend_idx = model.evaluate(friends[i]).as_long()
        if friend_idx != 9:
            start_time = model.evaluate(starts[i]).as_long()
            end_time = model.evaluate(ends[i]).as_long()
            friend_name = friends_data[friend_idx]['name']
            location = friends_locations[friend_idx]
            # Convert start and end times to H:MM format
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend_name,
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })
    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")