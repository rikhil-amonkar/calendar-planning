import itertools
from z3 import Solver, Int, Distinct, If, And, Or, Not, sat

# Define travel times dictionary
travel_time_dict = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15
}

# Friend data
friends = ['Ronald', 'Helen', 'Joshua', 'Margaret']
locations = {
    'Ronald': 'Nob Hill',
    'Helen': 'The Castro',
    'Joshua': 'Sunset District',
    'Margaret': 'Haight-Ashbury'
}
durations = {
    'Ronald': 105,
    'Helen': 120,
    'Joshua': 90,
    'Margaret': 60
}
windows_start = {
    'Ronald': 600,    # 10:00
    'Helen': 810,     # 13:30
    'Joshua': 855,    # 14:15
    'Margaret': 615   # 10:15
}
windows_end = {
    'Ronald': 1020,   # 17:00
    'Helen': 1020,    # 17:00
    'Joshua': 1170,   # 19:30
    'Margaret': 1320  # 22:00
}

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def schedule_subset(subset):
    s = Solver()
    s_var = {}
    e_var = {}
    pos_var = {}
    for friend in subset:
        s_var[friend] = Int(f's_{friend}')
        e_var[friend] = Int(f'e_{friend}')
        pos_var[friend] = Int(f'pos_{friend}')
    
    k = len(subset)
    
    # Time window and duration constraints
    for friend in subset:
        s.add(s_var[friend] >= windows_start[friend])
        s.add(e_var[friend] <= windows_end[friend])
        s.add(e_var[friend] == s_var[friend] + durations[friend])
    
    # Position constraints: distinct and in [1, k]
    s.add(Distinct([pos_var[friend] for friend in subset]))
    for friend in subset:
        s.add(pos_var[friend] >= 1)
        s.add(pos_var[friend] <= k)
    
    # Travel constraints
    for j in subset:
        # If j is first, travel from Pacific Heights to j
        s.add(If(pos_var[j] == 1, 
                s_var[j] >= 540 + travel_time_dict[('Pacific Heights', locations[j])], 
                True))
        for i in subset:
            if i == j:
                continue
            # If j comes immediately after i
            s.add(If(pos_var[j] == pos_var[i] + 1,
                     s_var[j] >= e_var[i] + travel_time_dict[(locations[i], locations[j])],
                     True))
    
    if s.check() == sat:
        model = s.model()
        schedule_list = []
        for friend in subset:
            start_val = model.evaluate(s_var[friend])
            if not isinstance(start_val, int):
                start_val = start_val.as_long()
            start_minutes = int(str(start_val))
            end_minutes = start_minutes + durations[friend]
            start_time = minutes_to_time(start_minutes)
            end_time = minutes_to_time(end_minutes)
            schedule_list.append({
                "action": "meet",
                "person": friend,
                "start_time": start_time,
                "end_time": end_time
            })
        # Sort by start time
        schedule_list.sort(key=lambda x: x['start_time'])
        return schedule_list
    else:
        return None

# Main loop to find the largest feasible subset
result_schedule = None
for k in range(4, 0, -1):
    for subset in itertools.combinations(friends, k):
        schedule = schedule_subset(subset)
        if schedule is not None:
            result_schedule = schedule
            break
    if result_schedule is not None:
        break

# Prepare output
if result_schedule is None:
    output = {"itinerary": []}
else:
    output = {"itinerary": result_schedule}

print("SOLUTION:")
print(output)