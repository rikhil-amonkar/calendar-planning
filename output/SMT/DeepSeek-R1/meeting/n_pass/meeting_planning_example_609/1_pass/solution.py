from z3 import *
import itertools
import json

# Friend data: (name, location, min_duration, availability_start_shifted, availability_end_shifted)
friends_data = [
    ("David", "Mission District", 45, -60, 645),
    ("Kenneth", "Alamo Square", 120, 300, 645),
    ("John", "Pacific Heights", 15, 480, 660),
    ("Charles", "Union Square", 60, 765, 825),
    ("Deborah", "Golden Gate Park", 90, -120, 555),
    ("Karen", "Sunset District", 15, 525, 735)
]

# Travel times between locations
travel_dict = {
    'Chinatown': {
        'Mission District': 18,
        'Alamo Square': 17,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Sunset District': 29
    },
    'Mission District': {
        'Chinatown': 16,
        'Alamo Square': 11,
        'Pacific Heights': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Sunset District': 24
    },
    'Alamo Square': {
        'Chinatown': 16,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Union Square': 14,
        'Golden Gate Park': 9,
        'Sunset District': 16
    },
    'Pacific Heights': {
        'Chinatown': 11,
        'Mission District': 15,
        'Alamo Square': 10,
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Sunset District': 21
    },
    'Union Square': {
        'Chinatown': 7,
        'Mission District': 14,
        'Alamo Square': 15,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'Sunset District': 26
    },
    'Golden Gate Park': {
        'Chinatown': 23,
        'Mission District': 17,
        'Alamo Square': 10,
        'Pacific Heights': 16,
        'Union Square': 22,
        'Sunset District': 10
    },
    'Sunset District': {
        'Chinatown': 30,
        'Mission District': 24,
        'Alamo Square': 17,
        'Pacific Heights': 21,
        'Union Square': 30,
        'Golden Gate Park': 11
    }
}

found = False
result_schedule = None

# Iterate over subset sizes from 6 down to 1
for k in range(6, 0, -1):
    for subset in itertools.combinations(friends_data, k):
        M = [('start', 'Chinatown', 0, None, None)]
        M.extend(subset)
        n = len(M)
        
        s = Solver()
        start_times = [Int(f'start_{i}') for i in range(n)]
        s.add(start_times[0] == 0)
        
        b = {}
        for i in range(n):
            for j in range(n):
                if i != j:
                    b[(i, j)] = Bool(f'b_{i}_{j}')
        
        # Total order constraints: antisymmetry and totality
        for i in range(n):
            for j in range(i + 1, n):
                s.add(Or(b[(i, j)], b[(j, i)]))
                s.add(b[(i, j)] == Not(b[(j, i)]))
        
        # Transitivity
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                for k in range(n):
                    if i == k or j == k:
                        continue
                    s.add(Implies(And(b[(i, j)], b[(j, k)]), b[(i, k)]))
        
        # Availability constraints
        for i in range(1, n):
            _, _, dur, avail_start, avail_end = M[i]
            s.add(start_times[i] >= avail_start)
            s.add(start_times[i] + dur <= avail_end)
        
        # Travel constraints
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                dur_i = 0 if i == 0 else M[i][2]
                loc_i = M[i][1]
                loc_j = M[j][1]
                tt = travel_dict[loc_i][loc_j]
                s.add(Implies(b[(i, j)], start_times[j] >= start_times[i] + dur_i + tt))
        
        if s.check() == sat:
            m = s.model()
            meetings = []
            for i in range(1, n):
                name, _, dur, _, _ = M[i]
                start_val = m[start_times[i]].as_long()
                hour = 9 + start_val // 60
                minute = start_val % 60
                start_str = f"{hour:02d}:{minute:02d}"
                end_val = start_val + dur
                hour_end = 9 + end_val // 60
                minute_end = end_val % 60
                end_str = f"{hour_end:02d}:{minute_end:02d}"
                meetings.append((start_val, name, start_str, end_str))
            
            meetings.sort(key=lambda x: x[0])
            itinerary = []
            for _, name, start_str, end_str in meetings:
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
            
            found = True
            result_schedule = itinerary
            break
    if found:
        break

if found:
    output = {"itinerary": result_schedule}
else:
    output = {"itinerary": []}

print("SOLUTION:")
print(json.dumps(output))