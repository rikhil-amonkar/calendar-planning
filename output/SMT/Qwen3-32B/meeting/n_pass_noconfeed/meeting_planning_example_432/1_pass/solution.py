import z3
import json

# Define friends
friends = [
    {'name': 'Joseph', 'location': "Fisherman's Wharf", 'available_start': 480, 'available_end': 1050, 'min_duration': 90},
    {'name': 'Jeffrey', 'location': 'Bayview', 'available_start': 1050, 'available_end': 1290, 'min_duration': 60},
    {'name': 'Kevin', 'location': 'Mission District', 'available_start': 675, 'available_end': 915, 'min_duration': 30},
    {'name': 'David', 'location': 'Embarcadero', 'available_start': 495, 'available_end': 540, 'min_duration': 30},
    {'name': 'Barbara', 'location': 'Financial District', 'available_start': 630, 'available_end': 990, 'min_duration': 15}
]

# Define travel times between locations
travel_times = {
    'Golden Gate Park': {
        "Fisherman's Wharf": 24,
        'Bayview': 23,
        'Mission District': 17,
        'Embarcadero': 25,
        'Financial District': 26,
    },
    "Fisherman's Wharf": {
        'Golden Gate Park': 25,
        'Bayview': 26,
        'Mission District': 22,
        'Embarcadero': 8,
        'Financial District': 11,
    },
    'Bayview': {
        'Golden Gate Park': 22,
        "Fisherman's Wharf": 25,
        'Mission District': 13,
        'Embarcadero': 19,
        'Financial District': 19,
    },
    'Mission District': {
        'Golden Gate Park': 17,
        "Fisherman's Wharf": 22,
        'Bayview': 15,
        'Embarcadero': 19,
        'Financial District': 17,
    },
    'Embarcadero': {
        'Golden Gate Park': 25,
        "Fisherman's Wharf": 6,
        'Bayview': 21,
        'Mission District': 20,
        'Financial District': 5,
    },
    'Financial District': {
        'Golden Gate Park': 23,
        "Fisherman's Wharf": 10,
        'Bayview': 19,
        'Mission District': 17,
        'Embarcadero': 4,
    },
}

# Create Z3 variables
solver = z3.Optimize()

MAX_MEETINGS = 5

# Variables for the sequence of meetings
friend_seq = [z3.Int(f'friend_seq_{i}') for i in range(MAX_MEETINGS)]
start_seq = [z3.Int(f'start_seq_{i}') for i in range(MAX_MEETINGS)]
end_seq = [z3.Int(f'end_seq_{i}') for i in range(MAX_MEETINGS)]

# Add constraints that each friend_seq[i] is between 0 and 5 (0 means no friend, 1-5 are friends 0-4)
for i in range(MAX_MEETINGS):
    solver.add(z3.And(friend_seq[i] >= 0, friend_seq[i] <= 5))

# Ensure the sequence is contiguous: if a position has a friend, all previous positions must also have friends
for i in range(1, MAX_MEETINGS):
    solver.add(z3.Implies(friend_seq[i] != 0, friend_seq[i-1] != 0))

# Add constraints for each position in the sequence
for i in range(MAX_MEETINGS):
    # For each possible friend p in this position
    for p in range(len(friends)):
        # If friend_seq[i] == p+1 (i.e., friend p is at this position)
        cond = z3.And(friend_seq[i] == p+1)
        
        if i == 0:
            # First meeting: travel from Golden Gate Park to friend's location
            from_loc = 'Golden Gate Park'
            to_loc = friends[p]['location']
            tt = travel_times[from_loc][to_loc]
            # start_seq[i] >= 540 (arrival time) + travel time
            solver.add(z3.Implies(cond, start_seq[i] >= 540 + tt))
        else:
            # For i > 0, travel from previous friend's location
            # Need to check all possible previous friends q
            for q in range(len(friends)):
                prev_cond = z3.And(friend_seq[i-1] == q+1)
                combined_cond = z3.And(prev_cond, cond)
                from_loc = friends[q]['location']
                to_loc = friends[p]['location']
                tt = travel_times[from_loc][to_loc]
                solver.add(z3.Implies(combined_cond, start_seq[i] >= end_seq[i-1] + tt))
        
        # Add constraints for available time and duration
        available_start = friends[p]['available_start']
        available_end = friends[p]['available_end']
        min_duration = friends[p]['min_duration']
        solver.add(z3.Implies(cond, start_seq[i] >= available_start))
        solver.add(z3.Implies(cond, start_seq[i] + min_duration <= available_end))
        solver.add(z3.Implies(cond, end_seq[i] == start_seq[i] + min_duration))

# Ensure each friend appears at most once
for p in range(len(friends)):
    count = 0
    for i in range(MAX_MEETINGS):
        count += z3.If(friend_seq[i] == p+1, 1, 0)
    solver.add(count <= 1)

# Objective: maximize the number of friends in the sequence
objective = 0
for i in range(MAX_MEETINGS):
    objective += z3.If(friend_seq[i] != 0, 1, 0)
solver.maximize(objective)

# Check if the problem is satisfiable
result = solver.check()
if result == z3.sat:
    model = solver.model()
    # Extract the sequence of meetings
    itinerary = []
    for i in range(MAX_MEETINGS):
        friend_idx = model.eval(friend_seq[i]).as_long()
        if friend_idx != 0:
            p = friend_idx - 1
            start = model.eval(start_seq[i]).as_long()
            end = model.eval(end_seq[i]).as_long()
            friend = friends[p]
            # Convert start and end times to H:MM format
            def to_time(mins):
                hours = mins // 60
                minutes = mins % 60
                return f"{hours}:{minutes:02d}"
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": to_time(start),
                "end_time": to_time(end)
            })
    # Output the JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))