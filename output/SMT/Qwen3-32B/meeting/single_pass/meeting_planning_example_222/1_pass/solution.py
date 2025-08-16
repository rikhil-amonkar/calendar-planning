import json
from itertools import permutations
from z3 import Solver, Int, sat, ModelRef

friends = ['Helen', 'Kimberly', 'Patricia']

friend_constraints = {
    'Helen': {
        'available_start': 7*60,  # 7:00 AM
        'available_end': 16*60 +45, # 4:45 PM
        'duration': 120,
        'location': 'North Beach'
    },
    'Kimberly': {
        'available_start': 16*60 +30, #4:30 PM
        'available_end': 21*60, #9:00 PM
        'duration':45,
        'location': "Fisherman's Wharf"
    },
    'Patricia': {
        'available_start': 18*60, #6:00 PM
        'available_end': 21*60 +15, #9:15 PM
        'duration':120,
        'location': 'Bayview'
    }
}

travel_times = {
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', "Fisherman's Wharf"): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('North Beach', 'Nob Hill'):7,
    ('North Beach', "Fisherman's Wharf"):5,
    ('North Beach', 'Bayview'):22,
    ("Fisherman's Wharf", 'Nob Hill'):11,
    ("Fisherman's Wharf", 'North Beach'):6,
    ("Fisherman's Wharf", 'Bayview'):26,
    ('Bayview', 'Nob Hill'):20,
    ('Bayview', 'North Beach'):21,
    ('Bayview', "Fisherman's Wharf"):25,
}

initial_time = 9 * 60  # 540 minutes (9:00 AM)

best_solution = None

for perm in permutations(friends):
    solver = Solver()
    start_times = {friend: Int(f"{friend}_start") for friend in perm}
    prev_end = initial_time
    prev_loc = 'Nob Hill'
    feasible = True

    for i, friend in enumerate(perm):
        f_data = friend_constraints[friend]
        friend_loc = f_data['location']
        duration = f_data['duration']
        avail_start = f_data['available_start']
        avail_end = f_data['available_end']

        travel_time = travel_times.get( (prev_loc, friend_loc), None )
        if travel_time is None:
            feasible = False
            break

        arrival_time = prev_end + travel_time
        s = start_times[friend]

        solver.add( s >= arrival_time )
        solver.add( s >= avail_start )
        solver.add( s + duration <= avail_end )

        prev_end = s + duration
        prev_loc = friend_loc

    if not feasible:
        continue

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for friend in perm:
            s_val = model.evaluate(start_times[friend]).as_long()
            duration = friend_constraints[friend]['duration']
            end_val = s_val + duration
            start_time = f"{(s_val // 60):02d}:{(s_val % 60):02d}"
            end_time = f"{(end_val // 60):02d}:{(end_val % 60):02d}"
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": start_time,
                "end_time": end_time
            })
        best_solution = {"itinerary": itinerary}
        break  # Found a solution, exit loops

if best_solution:
    print(json.dumps(best_solution, indent=2))
else:
    # Handle cases where no solution meets all friends
    pass