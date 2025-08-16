from z3 import *
import json

def get_travel_time(loc1, loc2):
    travel_times = {
        # Castro to others
        ('Castro', 'Presidio'): 20,
        ('Castro', 'Sunset District'): 17,
        ('Castro', 'Haight-Ashbury'): 6,
        ('Castro', 'Mission District'): 7,
        ('Castro', 'Golden Gate Park'): 11,
        ('Castro', 'Russian Hill'): 18,
        # Presidio to others
        ('Presidio', 'Castro'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Russian Hill'): 14,
        # Sunset District to others
        ('Sunset District', 'Castro'): 17,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Russian Hill'): 24,
        # Haight-Ashbury to others
        ('Haight-Ashbury', 'Castro'): 6,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        # Mission District to others
        ('Mission District', 'Castro'): 7,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Russian Hill'): 15,
        # Golden Gate Park to others
        ('Golden Gate Park', 'Castro'): 13,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Russian Hill'): 19,
        # Russian Hill to others
        ('Russian Hill', 'Castro'): 21,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Golden Gate Park'): 21,
    }
    return travel_times.get((loc1, loc2), 0)

friends_data = [
    {'name': 'Mark', 'location': 'Russian Hill', 'required': 75, 'available_start': 600, 'available_end': 1095},
    {'name': 'William', 'location': 'Mission District', 'required': 30, 'available_start': 795, 'available_end': 1170},
    {'name': 'Robert', 'location': 'Golden Gate Park', 'required': 45, 'available_start': 1335, 'available_end': 1170},
    {'name': 'Linda', 'location': 'Sunset District', 'required': 30, 'available_start': 930, 'available_end': 1185},
    {'name': 'Elizabeth', 'location': 'Haight-Ashbury', 'required': 105, 'available_start': 1035, 'available_end': 1170},
    {'name': 'Rebecca', 'location': 'Presidio', 'required': 60, 'available_start': 1095, 'available_end': 1245}
]

s = Solver()
n = len(friends_data)

order = [Int(f'order_{i}') for i in range(n)]
start_time = [Int(f'start_{i}') for i in range(n)]
end_time = [Int(f'end_{i}') for i in range(n)]

for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

for i in range(n):
    required = friends_data[i]['required']
    s.add(end_time[i] == start_time[i] + required)

for i in range(n):
    loc_i = friends_data[i]['location']
    travel_time_castro = get_travel_time('Castro', loc_i)
    s.add(Implies(order[i] == 0, start_time[i] >= 540 + travel_time_castro))

for i in range(n):
    for j in range(n):
        if i != j:
            loc_i = friends_data[i]['location']
            loc_j = friends_data[j]['location']
            travel_time = get_travel_time(loc_i, loc_j)
            if travel_time:
                s.add(Implies(order[i] < order[j], start_time[j] >= end_time[i] + travel_time))

for i in range(n):
    available_start = friends_data[i]['available_start']
    available_end = friends_data[i]['available_end']
    required = friends_data[i]['required']
    s.add(start_time[i] >= available_start)
    s.add(start_time[i] + required <= available_end)

if s.check() == sat:
    m = s.model()
    seq = [m.eval(order[i]).as_long() for i in range(n)]
    friend_order = sorted(range(n), key=lambda x: seq[x])
    itinerary = []
    for idx in friend_order:
        friend = friends_data[idx]
        start = m.eval(start_time[idx]).as_long()
        end = m.eval(end_time[idx]).as_long()
        def to_time(mins):
            h = mins // 60
            m = mins % 60
            return f"{h:02d}:{m:02d}"
        start_str = to_time(start)
        end_str = to_time(end)
        itinerary.append({
            "action": "meet", 
            "person": friend['name'], 
            "start_time": start_str, 
            "end_time": end_str
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")