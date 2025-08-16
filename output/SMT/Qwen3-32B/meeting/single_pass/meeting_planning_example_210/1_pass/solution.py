from z3 import *
from itertools import permutations, combinations

# Define friends' data
friends_data = {
    'Emily': {
        'location': 'Presidio',
        'available_start': 16 * 60 + 15,  # 975
        'available_end': 21 * 60,         # 1260 (21:00)
        'min_duration': 105
    },
    'Joseph': {
        'location': 'Richmond District',
        'available_start': 17 * 60 + 15,  # 1035
        'available_end': 22 * 60,         # 1320 (22:00)
        'min_duration': 120
    },
    'Melissa': {
        'location': 'Financial District',
        'available_start': 15 * 60 + 45,  # 945
        'available_end': 21 * 60 + 45,    # 1305 (21:45)
        'min_duration': 75
    }
}

# Travel times between locations
travel_times = {
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Financial District'): 22,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Richmond District'): 21,
}

friends_list = ['Emily', 'Joseph', 'Melissa']
best_solution = None
max_friends = 0

# Check all possible permutations in descending order of subset size
for k in range(3, 0, -1):
    for subset in combinations(friends_list, k):
        for perm in permutations(subset):
            s = Solver()
            start_vars = {}
            end_vars = {}
            for friend in perm:
                start_vars[friend] = Int(f'start_{friend}')
                end_vars[friend] = Int(f'end_{friend}')
            prev_loc = 'Fisherman\'s Wharf'
            prev_end = 9 * 60  # 540 minutes (9:00 AM)
            feasible = True
            for friend in perm:
                friend_info = friends_data[friend]
                curr_loc = friend_info['location']
                travel_time = travel_times.get((prev_loc, curr_loc), None)
                if travel_time is None:
                    feasible = False
                    break
                arrival_time = prev_end + travel_time
                start = start_vars[friend]
                end = end_vars[friend]
                s.add(start >= arrival_time)
                s.add(start >= friend_info['available_start'])
                s.add(end == start + friend_info['min_duration'])
                s.add(end <= friend_info['available_end'])
                prev_loc = curr_loc
                prev_end = end
            if not feasible:
                continue
            if s.check() == sat:
                model = s.model()
                if k > max_friends:
                    max_friends = k
                    best_solution = {
                        'perm': perm,
                        'model': model,
                        'start_vars': start_vars,
                        'end_vars': end_vars
                    }
                # Early exit if maximum possible is achieved
                if k == 3:
                    # No need to check further
                    break
            # Check if we found a solution for k=3 and can exit
            if best_solution and max_friends == 3:
                break
        if best_solution and max_friends == 3:
            break
    if best_solution and max_friends == 3:
        break

# Generate the itinerary
itinerary = []
if best_solution:
    model = best_solution['model']
    start_vars = best_solution['start_vars']
    end_vars = best_solution['end_vars']
    for friend in best_solution['perm']:
        start_time = model.eval(start_vars[friend]).as_long()
        end_time = model.eval(end_vars[friend]).as_long()
        start_str = f"{start_time//60:02d}:{start_time%60:02d}"
        end_str = f"{end_time//60:02d}:{end_time%60:02d}"
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": start_str,
            "end_time": end_str
        })

# Output the JSON-formatted solution
solution = {"itinerary": itinerary}
print("SOLUTION:")
print(solution)