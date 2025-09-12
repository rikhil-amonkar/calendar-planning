import z3
from itertools import permutations
import json

def minutes_to_time_str(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

friends = [
    {
        'name': 'Barbara',
        'location': 'Fisherman\'s Wharf',
        'available_start': 555,  # 9:15 AM
        'available_end': 1215,   # 8:15 PM
        'min_duration': 120
    },
    {
        'name': 'Betty',
        'location': 'Presidio',
        'available_start': 615,  # 10:15 AM
        'available_end': 1290,   # 9:30 PM
        'min_duration': 45
    },
    {
        'name': 'David',
        'location': 'Richmond District',
        'available_start': 780,  # 1:00 PM
        'available_end': 1215,   # 8:15 PM
        'min_duration': 90
    }
]

itinerary = []
found = False

for perm_length in [3, 2, 1]:
    for perm in permutations(friends, perm_length):
        S = [z3.Int(f'S_{i}') for i in range(perm_length)]
        E = [z3.Int(f'E_{i}') for i in range(perm_length)]
        solver = z3.Solver()
        prev_end = 540  # start time at Embarcadero
        prev_loc = 'Embarcadero'
        for i in range(perm_length):
            current_friend = perm[i]
            current_loc = current_friend['location']
            travel_time_val = travel_times[(prev_loc, current_loc)]
            if i == 0:
                arrival_time = 540 + travel_time_val
            else:
                arrival_time = E[i-1] + travel_time_val
            # Add constraints
            solver.add(S[i] >= z3.Max(arrival_time, current_friend['available_start']))
            solver.add(E[i] == S[i] + current_friend['min_duration'])
            solver.add(E[i] <= current_friend['available_end'])
            # Update for next iteration
            prev_end = E[i]
            prev_loc = current_loc
        if str(solver.check()) == 'sat':
            model = solver.model()
            itinerary = []
            for i in range(perm_length):
                start = model.evaluate(S[i]).as_long()
                end = model.evaluate(E[i]).as_long()
                friend = perm[i]
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time_str(start),
                    "end_time": minutes_to_time_str(end)
                })
            found = True
            break
        if found:
            break
    if found:
        break

# Output the JSON
print(json.dumps({"itinerary": itinerary}, indent=2))