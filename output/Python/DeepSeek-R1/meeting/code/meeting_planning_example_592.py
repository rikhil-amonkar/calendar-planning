import json
from itertools import permutations

def time_to_min(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

travel_times = {
    'North Beach': {'Pacific Heights':8, 'Chinatown':6, 'Union Square':7, 'Mission District':18, 'Golden Gate Park':22, 'Nob Hill':7},
    'Pacific Heights': {'North Beach':9, 'Chinatown':11, 'Union Square':12, 'Mission District':15, 'Golden Gate Park':15, 'Nob Hill':8},
    'Chinatown': {'North Beach':3, 'Pacific Heights':10, 'Union Square':7, 'Mission District':18, 'Golden Gate Park':23, 'Nob Hill':8},
    'Union Square': {'North Beach':10, 'Pacific Heights':15, 'Chinatown':7, 'Mission District':14, 'Golden Gate Park':22, 'Nob Hill':9},
    'Mission District': {'North Beach':17, 'Pacific Heights':16, 'Chinatown':16, 'Union Square':15, 'Golden Gate Park':17, 'Nob Hill':12},
    'Golden Gate Park': {'North Beach':24, 'Pacific Heights':16, 'Chinatown':23, 'Union Square':22, 'Mission District':17, 'Nob Hill':20},
    'Nob Hill': {'North Beach':8, 'Pacific Heights':8, 'Chinatown':6, 'Union Square':7, 'Mission District':13, 'Golden Gate Park':17}
}

friends = [
    {'name':'Jeffrey', 'loc':'Union Square', 'start':time_to_min('9:30'), 'end':time_to_min('15:30'), 'dur':120},
    {'name':'Robert', 'loc':'Chinatown', 'start':time_to_min('12:15'), 'end':time_to_min('16:45'), 'dur':90},
    {'name':'Sandra', 'loc':'Nob Hill', 'start':time_to_min('8:00'), 'end':time_to_min('15:30'), 'dur':15},
    {'name':'Mark', 'loc':'Golden Gate Park', 'start':time_to_min('11:30'), 'end':time_to_min('17:45'), 'dur':15},
    {'name':'Carol', 'loc':'Mission District', 'start':time_to_min('18:15'), 'end':time_to_min('21:15'), 'dur':15},
    {'name':'James', 'loc':'Pacific Heights', 'start':time_to_min('20:00'), 'end':time_to_min('22:00'), 'dur':120}
]

non_james = [f for f in friends if f['name'] != 'James']
best = []

for order in permutations(non_james):
    schedule = []
    current = 'North Beach'
    time = time_to_min('9:00')
    valid = True
    
    for friend in order:
        travel = travel_times[current][friend['loc']]
        arrive = time + travel
        start = max(arrive, friend['start'])
        if start + friend['dur'] > friend['end']:
            valid = False
            break
        schedule.append({
            'action':'meet', 'location':friend['loc'], 'person':friend['name'],
            'start_time':min_to_time(start).replace(':0', ':') if min_to_time(start).endswith(':00') else min_to_time(start),
            'end_time':min_to_time(start + friend['dur']).replace(':0', ':') if min_to_time(start + friend['dur']).endswith(':00') else min_to_time(start + friend['dur'])
        })
        time = start + friend['dur']
        current = friend['loc']
    
    if valid:
        james_travel = travel_times[current]['Pacific Heights']
        arrive_j = time + james_travel
        start_j = max(arrive_j, friends[-1]['start'])
        if start_j + friends[-1]['dur'] > friends[-1]['end']:
            continue
        schedule.append({
            'action':'meet', 'location':'Pacific Heights', 'person':'James',
            'start_time':min_to_time(start_j).replace(':0', ':') if min_to_time(start_j).endswith(':00') else min_to_time(start_j),
            'end_time':min_to_time(start_j + 120).replace(':0', ':') if min_to_time(start_j + 120).endswith(':00') else min_to_time(start_j + 120)
        })
        if len(schedule) > len(best):
            best = schedule

print(json.dumps({'itinerary': best}, indent=2))