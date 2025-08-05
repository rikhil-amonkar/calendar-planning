from z3 import *
import json

def main():
    meetings = [
        (0, "Start", "Pacific Heights", 540, 540, 0, True),
        (1, "Linda", "Marina District", 1080, 1320, 30, None),
        (2, "Kenneth", "The Castro", 885, 975, 30, None),
        (3, "Kimberly", "Richmond District", 855, 1320, 30, None),
        (4, "Paul", "Alamo Square", 1260, 1290, 15, None),
        (5, "Carol", "Financial District", 615, 720, 60, None),
        (6, "Brian", "Presidio", 600, 1290, 75, None),
        (7, "Laura", "Mission District", 975, 1230, 30, None),
        (8, "Sandra", "Nob Hill", 555, 1110, 60, None),
        (9, "Karen", "Russian Hill", 1110, 1320, 75, None)
    ]
    
    travel_times = {
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Russian Hill'): 8,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Financial District'): 21,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Russian Hill'): 18,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Russian Hill'): 13,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'The Castro'): 20,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Russian Hill'): 11,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Financial District'): 15,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Russian Hill'): 15,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Financial District'): 11,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Nob Hill'): 5
    }
    
    s = [Int(f's_{i}') for i in range(10)]
    b = [Bool(f'b_{i}') for i in range(1, 10)]
    locations = [m[2] for m in meetings]
    durations = [m[5] for m in meetings]
    
    opt = Optimize()
    
    opt.add(s[0] == 540)
    
    for i in range(1, 10):
        avail_start = meetings[i][3]
        avail_end = meetings[i][4]
        min_dur = meetings[i][5]
        opt.add(Implies(b[i-1], And(s[i] >= avail_start, s[i] + min_dur <= avail_end)))
    
    for i in range(0, 10):
        for j in range(i+1, 10):
            cond_i = True
            cond_j = True
            if i != 0:
                cond_i = b[i-1]
            if j != 0:
                cond_j = b[j-1]
            loc_i = locations[i]
            loc_j = locations[j]
            travel_ij = travel_times[(loc_i, loc_j)]
            travel_ji = travel_times[(loc_j, loc_i)]
            dur_i = durations[i]
            dur_j = durations[j]
            opt.add(Implies(And(cond_i, cond_j),
                           Or(s[i] + dur_i + travel_ij <= s[j],
                              s[j] + dur_j + travel_ji <= s[i])))
    
    num_meetings = Sum([If(b_i, 1, 0) for b_i in b])
    opt.maximize(num_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for idx in range(1, 10):
            if model.evaluate(b[idx-1]):
                start_val = model.evaluate(s[idx])
                if isinstance(start_val, IntNumRef):
                    start_minutes = start_val.as_long()
                else:
                    start_minutes = int(str(start_val))
                h = start_minutes // 60
                m = start_minutes % 60
                start_time = f"{h:02d}:{m:02d}"
                end_minutes = start_minutes + meetings[idx][5]
                h_end = end_minutes // 60
                m_end = end_minutes % 60
                end_time = f"{h_end:02d}:{m_end:02d}"
                scheduled_meetings.append({
                    "action": "meet",
                    "person": meetings[idx][1],
                    "start_time": start_time,
                    "end_time": end_time
                })
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": scheduled_meetings}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()