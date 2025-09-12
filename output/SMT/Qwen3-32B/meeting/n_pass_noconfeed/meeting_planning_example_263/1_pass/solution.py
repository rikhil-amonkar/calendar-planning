import itertools
import z3
import json

# Define travel times between locations (in minutes)
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Financial District'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
}

# Define friend constraints
friends = [
    {
        'name': 'Karen',
        'location': 'Fisherman\'s Wharf',
        'available_start': 8 * 60 + 45,  # 8:45 AM
        'available_end': 15 * 60,        # 3:00 PM
        'min_duration': 30
    },
    {
        'name': 'Anthony',
        'location': 'Financial District',
        'available_start': 9 * 60 + 15,  # 9:15 AM
        'available_end': 21 * 60 + 30,   # 9:30 PM
        'min_duration': 105
    },
    {
        'name': 'Betty',
        'location': 'Embarcadero',
        'available_start': 19 * 60 + 45, # 7:45 PM
        'available_end': 21 * 60 + 45,   # 9:45 PM
        'min_duration': 15
    }
]

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_permutation_feasible(perm):
    solver = z3.Solver()
    
    for i, friend in enumerate(perm):
        st = z3.Int(f"{friend['name']}_start")
        et = st + friend['min_duration']
        solver.add(st >= friend['available_start'])
        solver.add(et <= friend['available_end'])
        
    prev_end = 540  # 9:00 AM at Bayview
    prev_loc = 'Bayview'
    
    for i, friend in enumerate(perm):
        current_loc = friend['location']
        travel_time = travel_times[(prev_loc, current_loc)]
        arrival_time = prev_end + travel_time
        st = z3.Int(f"{friend['name']}_start")
        solver.add(st >= arrival_time)
        prev_end = st + friend['min_duration']
        prev_loc = current_loc
    
    if solver.check() == z3.sat:
        return (True, solver.model())
    else:
        return (False, None)

def main():
    best_perm = None
    best_model = None
    
    # Check permutations of 3 friends
    for perm in itertools.permutations(friends, 3):
        feasible, model = is_permutation_feasible(perm)
        if feasible:
            best_perm = perm
            best_model = model
            break
    
    # If no 3-friend solution, check permutations of 2 friends
    if not best_perm:
        for perm in itertools.permutations(friends, 2):
            feasible, model = is_permutation_feasible(perm)
            if feasible:
                best_perm = perm
                best_model = model
                break
    
    # If no 2-friend solution, check permutations of 1 friend
    if not best_perm:
        for perm in itertools.permutations(friends, 1):
            feasible, model = is_permutation_feasible(perm)
            if feasible:
                best_perm = perm
                best_model = model
                break
    
    if not best_perm:
        print(json.dumps({"itinerary": []}))
        return
    
    # Build itinerary from best solution
    itinerary = []
    for friend in best_perm:
        st = best_model.evaluate(z3.Int(f"{friend['name']}_start")).as_long()
        et = st + friend['min_duration']
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time_str(st),
            "end_time": minutes_to_time_str(et)
        })
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()