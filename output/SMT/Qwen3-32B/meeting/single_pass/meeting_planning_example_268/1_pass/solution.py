import json
from z3 import *

travel_times = {
    ('GGP', 'AS'): 10,
    ('AS', 'GGP'): 9,
    ('GGP', 'P'): 11,
    ('P', 'GGP'): 12,
    ('GGP', 'RH'): 19,
    ('RH', 'GGP'): 21,
    ('AS', 'P'): 18,
    ('P', 'AS'): 18,
    ('AS', 'RH'): 13,
    ('RH', 'AS'): 15,
    ('P', 'RH'): 14,
    ('RH', 'P'): 14,
}

friends_locations = {
    'Timothy': 'AS',
    'Mark': 'P',
    'Joseph': 'RH'
}

availability = {
    'Timothy': (720, 975),  # 12:00 PM to 4:15 PM
    'Mark': (1125, 1260),   # 6:45 PM to 9:00 PM
    'Joseph': (1005, 1290)  # 4:45 PM to 9:30 PM
}

durations = {
    'Timothy': 105,
    'Mark': 60,
    'Joseph': 60
}

permutations = [
    ['Timothy', 'Joseph', 'Mark'],
    ['Timothy', 'Mark', 'Joseph']
]

def solve_permutation(perm):
    s = Solver()
    starts = {}
    ends = {}
    current_time = 540  # 9:00 AM
    current_loc = 'GGP'
    for friend in perm:
        loc = friends_locations[friend]
        travel_time = travel_times[(current_loc, loc)]
        arrival_time = current_time + travel_time
        start_var = Int(f"start_{friend}")
        end_var = start_var + durations[friend]
        # Add constraints
        s.add(start_var >= arrival_time)
        s.add(start_var >= availability[friend][0])
        s.add(end_var <= availability[friend][1])
        starts[friend] = start_var
        ends[friend] = end_var
        # Update for next step
        current_time = end_var
        current_loc = loc
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in perm:
            start = model.evaluate(starts[friend]).as_long()
            end = model.evaluate(ends[friend]).as_long()
            start_time = f"{start//60:02d}:{start%60:02d}"
            end_time = f"{end//60:02d}:{end%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": start_time,
                "end_time": end_time
            })
        return {"itinerary": itinerary}
    else:
        return None

# Check permutations
result = None
for perm in permutations:
    res = solve_permutation(perm)
    if res is not None:
        result = res
        break

print(json.dumps(result))