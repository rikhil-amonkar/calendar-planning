from z3 import Int, Solver, sat
import itertools
import json

def min_to_time(minutes):
    total_minutes = 9 * 60 + minutes
    hours = total_minutes // 60
    minutes_part = total_minutes % 60
    return f"{hours:02d}:{minutes_part:02d}"

travel_time = {
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
    ('Fisherman\'s Wharf', 'Richmond District'): 18
}

friends_data = {
    'Betty': {
        'location': 'Presidio',
        'start_available': 75,   # 10:15 AM
        'end_available': 750,    # 9:30 PM
        'duration': 45
    },
    'David': {
        'location': 'Richmond District',
        'start_available': 240,  # 1:00 PM
        'end_available': 675,    # 8:15 PM
        'duration': 90
    },
    'Barbara': {
        'location': 'Fisherman\'s Wharf',
        'start_available': 15,   # 9:15 AM
        'end_available': 675,    # 8:15 PM
        'duration': 120
    }
}

friends_list = list(friends_data.keys())
itinerary = []

# Try to meet all three friends
found_three = False
for perm in itertools.permutations(friends_list, 3):
    s = Solver()
    s0 = Int(f's0_{perm[0]}')
    s1 = Int(f's1_{perm[1]}')
    s2 = Int(f's2_{perm[2]}')
    
    f0 = friends_data[perm[0]]
    f1 = friends_data[perm[1]]
    f2 = friends_data[perm[2]]
    
    travel0 = travel_time[('Embarcadero', f0['location'])]
    s.add(s0 >= travel0)
    s.add(s0 >= f0['start_available'])
    s.add(s0 + f0['duration'] <= f0['end_available'])
    
    travel1 = travel_time[(f0['location'], f1['location'])]
    s.add(s1 >= s0 + f0['duration'] + travel1)
    s.add(s1 >= f1['start_available'])
    s.add(s1 + f1['duration'] <= f1['end_available'])
    
    travel2 = travel_time[(f1['location'], f2['location'])]
    s.add(s2 >= s1 + f1['duration'] + travel2)
    s.add(s2 >= f2['start_available'])
    s.add(s2 + f2['duration'] <= f2['end_available'])
    
    if s.check() == sat:
        model = s.model()
        s0_val = model[s0].as_long()
        s1_val = model[s1].as_long()
        s2_val = model[s2].as_long()
        itinerary = [
            {"action": "meet", "person": perm[0], 
             "start_time": min_to_time(s0_val), 
             "end_time": min_to_time(s0_val + f0['duration'])},
            {"action": "meet", "person": perm[1], 
             "start_time": min_to_time(s1_val), 
             "end_time": min_to_time(s1_val + f1['duration'])},
            {"action": "meet", "person": perm[2], 
             "start_time": min_to_time(s2_val), 
             "end_time": min_to_time(s2_val + f2['duration'])}
        ]
        found_three = True
        break

if found_three:
    print(json.dumps({"itinerary": itinerary}))
    exit(0)

# Try to meet two friends
found_two = False
for subset in itertools.combinations(friends_list, 2):
    for perm in itertools.permutations(subset, 2):
        s = Solver()
        s0 = Int(f's0_{perm[0]}')
        s1 = Int(f's1_{perm[1]}')
        
        f0 = friends_data[perm[0]]
        f1 = friends_data[perm[1]]
        
        travel0 = travel_time[('Embarcadero', f0['location'])]
        s.add(s0 >= travel0)
        s.add(s0 >= f0['start_available'])
        s.add(s0 + f0['duration'] <= f0['end_available'])
        
        travel1 = travel_time[(f0['location'], f1['location'])]
        s.add(s1 >= s0 + f0['duration'] + travel1)
        s.add(s1 >= f1['start_available'])
        s.add(s1 + f1['duration'] <= f1['end_available'])
        
        if s.check() == sat:
            model = s.model()
            s0_val = model[s0].as_long()
            s1_val = model[s1].as_long()
            itinerary = [
                {"action": "meet", "person": perm[0], 
                 "start_time": min_to_time(s0_val), 
                 "end_time": min_to_time(s0_val + f0['duration'])},
                {"action": "meet", "person": perm[1], 
                 "start_time": min_to_time(s1_val), 
                 "end_time": min_to_time(s1_val + f1['duration'])}
            ]
            found_two = True
            break
    if found_two:
        break

if found_two:
    print(json.dumps({"itinerary": itinerary}))
    exit(0)

# Meet one friend
for friend in friends_list:
    s = Solver()
    s0 = Int(f's0_{friend}')
    f = friends_data[friend]
    travel0 = travel_time[('Embarcadero', f['location'])]
    s.add(s0 >= travel0)
    s.add(s0 >= f['start_available'])
    s.add(s0 + f['duration'] <= f['end_available'])
    
    if s.check() == sat:
        model = s.model()
        s0_val = model[s0].as_long()
        itinerary = [
            {"action": "meet", "person": friend, 
             "start_time": min_to_time(s0_val), 
             "end_time": min_to_time(s0_val + f['duration'])}
        ]
        break

print(json.dumps({"itinerary": itinerary}))