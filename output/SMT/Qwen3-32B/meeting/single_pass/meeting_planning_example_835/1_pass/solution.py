from z3 import *
import json

# Define friends with their details
friends = [
    {'name': 'Helen', 'location': 'Golden Gate Park', 'available_start': 9*60+30, 'available_end': 12*60+15, 'required': 45},
    {'name': 'Steven', 'location': 'The Castro', 'available_start': 20*60+15, 'available_end': 22*60+0, 'required': 105},
    {'name': 'Deborah', 'location': 'Bayview', 'available_start': 8*60+30, 'available_end': 12*60+0, 'required': 30},
    {'name': 'Matthew', 'location': 'Marina District', 'available_start': 9*60+15, 'available_end': 14*60+15, 'required': 45},
    {'name': 'Joseph', 'location': 'Union Square', 'available_start': 14*60+15, 'available_end': 18*60+45, 'required': 120},
    {'name': 'Ronald', 'location': 'Sunset District', 'available_start': 16*60+0, 'available_end': 20*60+45, 'required': 60},
    {'name': 'Robert', 'location': 'Alamo Square', 'available_start': 18*60+30, 'available_end': 21*60+15, 'required': 120},
    {'name': 'Rebecca', 'location': 'Financial District', 'available_start': 14*60+45, 'available_end': 16*60+15, 'required': 30},
    {'name': 'Elizabeth', 'location': 'Mission District', 'available_start': 18*60+30, 'available_end': 21*60+0, 'required': 120},
]

# Travel times dictionary
travel_time = {
    # Pacific Heights to others
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    # Golden Gate Park to others
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Mission District'): 17,
    # The Castro to others
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Mission District'): 7,
    # Bayview to others
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Mission District'): 13,
    # Marina District to others
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Mission District'): 20,
    # Union Square to others
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Mission District'): 14,
    # Sunset District to others
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Mission District'): 25,
    # Alamo Square to others
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    # Financial District to others
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    # Mission District to others
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Financial District'): 15,
}

# Precompute travel_time_matrix between friends
num_friends = len(friends)
travel_time_matrix = [[0 for _ in range(num_friends)] for _ in range(num_friends)]
for i in range(num_friends):
    for j in range(num_friends):
        loc_i = friends[i]['location']
        loc_j = friends[j]['location']
        travel_time_matrix[i][j] = travel_time[(loc_i, loc_j)]

# Precompute travel times from Pacific Heights to each friend
travel_time_pacific_to = [travel_time[('Pacific Heights', friends[i]['location'])] for i in range(num_friends)]

# Try from maximum possible number of friends down to 1
best_itinerary = None
for k in range(num_friends, 0, -1):
    solver = Optimize()
    friends_vars = [Int(f'friend_{i}') for i in range(k)]
    start_vars = [Int(f'start_{i}') for i in range(k)]
    end_vars = [Int(f'end_{i}') for i in range(k)]
    
    # All friends in sequence are distinct
    solver.add(Distinct(friends_vars))
    
    # Add constraints for each position
    for i in range(k):
        if i == 0:
            # Travel time from Pacific Heights
            tt0_expr = 0
            for idx in range(num_friends):
                tt0_expr = If(friends_vars[0] == idx, travel_time_pacific_to[idx], tt0_expr)
            solver.add(start_vars[0] >= 540 + tt0_expr)
        else:
            # Travel time from friend_{i-1} to friend_i
            tt_expr = 0
            for prev in range(num_friends):
                for curr in range(num_friends):
                    condition = And(friends_vars[i-1] == prev, friends_vars[i] == curr)
                    tt_expr = If(condition, travel_time_matrix[prev][curr], tt_expr)
            solver.add(start_vars[i] >= end_vars[i-1] + tt_expr)
        
        # Required duration
        required_expr = 0
        for idx in range(num_friends):
            required_expr = If(friends_vars[i] == idx, friends[idx]['required'], required_expr)
        solver.add(end_vars[i] == start_vars[i] + required_expr)
        
        # Available start and end
        available_start_expr = 0
        available_end_expr = 0
        for idx in range(num_friends):
            available_start_expr = If(friends_vars[i] == idx, friends[idx]['available_start'], available_start_expr)
            available_end_expr = If(friends_vars[i] == idx, friends[idx]['available_end'], available_end_expr)
        solver.add(start_vars[i] >= available_start_expr)
        solver.add(end_vars[i] <= available_end_expr)
    
    if solver.check() == sat:
        model = solver.model()
        # Extract the sequence
        sequence = []
        for i in range(k):
            friend_idx = model.eval(friends_vars[i])
            friend_idx = int(str(friend_idx))
            sequence.append(friend_idx)
        # Extract the start and end times
        itinerary = []
        for i in range(k):
            start = model.eval(start_vars[i])
            end = model.eval(end_vars[i])
            start_minutes = int(str(start))
            end_minutes = int(str(end))
            friend_idx = sequence[i]
            name = friends[friend_idx]['name']
            # Convert minutes to HH:MM
            start_time = f"{(start_minutes // 60):02d}:{(start_minutes % 60):02d}"
            end_time = f"{(end_minutes // 60):02d}:{(end_minutes % 60):02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        best_itinerary = {"itinerary": itinerary}
        break

# Output the best itinerary found
if best_itinerary:
    print(json.dumps(best_itinerary))
else:
    print("No solution found")