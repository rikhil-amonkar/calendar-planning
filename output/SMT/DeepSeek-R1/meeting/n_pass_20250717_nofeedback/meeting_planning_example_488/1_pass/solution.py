import z3
import json

def convert_time(minutes_since_900):
    total_minutes = minutes_since_900
    base_hour = 9
    hour = base_hour + total_minutes // 60
    minute = total_minutes % 60
    return f"{int(hour):02d}:{int(minute):02d}"

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

meetings = [
    {'name': 'Ronald', 'loc': 'Nob Hill', 'start_avail': 60, 'end_avail': 480, 'duration': 105},
    {'name': 'Margaret', 'loc': 'Haight-Ashbury', 'start_avail': 75, 'end_avail': 780, 'duration': 60},
    {'name': 'Helen', 'loc': 'The Castro', 'start_avail': 270, 'end_avail': 480, 'duration': 120},
    {'name': 'Joshua', 'loc': 'Sunset District', 'start_avail': 315, 'end_avail': 630, 'duration': 90}
]

durations = [105, 60, 120, 90]
locs = [m['loc'] for m in meetings]

travel_P = []
for i in range(4):
    from_loc = 'Pacific Heights'
    to_loc = locs[i]
    travel_P.append(travel_time_dict[(from_loc, to_loc)])

travel = [[0]*4 for _ in range(4)]
for i in range(4):
    for j in range(4):
        if i != j:
            from_loc = locs[i]
            to_loc = locs[j]
            travel[i][j] = travel_time_dict[(from_loc, to_loc)]

s0, s1, s2, s3 = z3.Ints('s0 s1 s2 s3')
p0, p1, p2, p3 = z3.Ints('p0 p1 p2 p3')
s = z3.Solver()

s.add(z3.Distinct(p0, p1, p2, p3))
s.add(p0 >= 0, p0 <= 3)
s.add(p1 >= 0, p1 <= 3)
s.add(p2 >= 0, p2 <= 3)
s.add(p3 >= 0, p3 <= 3)

s.add(s0 >= meetings[0]['start_avail'])
s.add(s0 + durations[0] <= meetings[0]['end_avail'])
s.add(s1 >= meetings[1]['start_avail'])
s.add(s1 + durations[1] <= meetings[1]['end_avail'])
s.add(s2 >= meetings[2]['start_avail'])
s.add(s2 + durations[2] <= meetings[2]['end_avail'])
s.add(s3 >= meetings[3]['start_avail'])
s.add(s3 + durations[3] <= meetings[3]['end_avail'])

s.add(z3.Implies(p0 == 0, s0 >= travel_P[0]))
s.add(z3.Implies(p1 == 0, s1 >= travel_P[1]))
s.add(z3.Implies(p2 == 0, s2 >= travel_P[2]))
s.add(z3.Implies(p3 == 0, s3 >= travel_P[3]))

s_list = [s0, s1, s2, s3]
p_list = [p0, p1, p2, p3]

for i in range(4):
    for j in range(4):
        if i != j:
            cond = (p_list[j] == p_list[i] + 1)
            s.add(z3.Implies(cond, s_list[j] >= s_list[i] + durations[i] + travel[i][j]))

if s.check() == z3.sat:
    model = s.model()
    s0_val = model.eval(s0).as_long()
    s1_val = model.eval(s1).as_long()
    s2_val = model.eval(s2).as_long()
    s3_val = model.eval(s3).as_long()
    
    schedule = []
    schedule.append({
        'person': 'Ronald',
        'start_time': convert_time(s0_val),
        'end_time': convert_time(s0_val + durations[0])
    })
    schedule.append({
        'person': 'Margaret',
        'start_time': convert_time(s1_val),
        'end_time': convert_time(s1_val + durations[1])
    })
    schedule.append({
        'person': 'Helen',
        'start_time': convert_time(s2_val),
        'end_time': convert_time(s2_val + durations[2])
    })
    schedule.append({
        'person': 'Joshua',
        'start_time': convert_time(s3_val),
        'end_time': convert_time(s3_val + durations[3])
    })
    
    schedule.sort(key=lambda x: x['start_time'])
    
    itinerary = []
    for entry in schedule:
        itinerary.append({
            "action": "meet",
            "person": entry['person'],
            "start_time": entry['start_time'],
            "end_time": entry['end_time']
        })
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))