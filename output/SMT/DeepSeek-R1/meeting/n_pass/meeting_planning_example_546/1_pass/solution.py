import json
from z3 import *

def main():
    locations = ['Embarcadero', 'Richmond District', 'Union Square', 'Financial District', 'Pacific Heights', 'Nob Hill', 'Bayview']
    
    travel_list = [
        ('Embarcadero', 'Richmond District', 21),
        ('Embarcadero', 'Union Square', 10),
        ('Embarcadero', 'Financial District', 5),
        ('Embarcadero', 'Pacific Heights', 11),
        ('Embarcadero', 'Nob Hill', 10),
        ('Embarcadero', 'Bayview', 21),
        ('Richmond District', 'Embarcadero', 19),
        ('Richmond District', 'Union Square', 21),
        ('Richmond District', 'Financial District', 22),
        ('Richmond District', 'Pacific Heights', 10),
        ('Richmond District', 'Nob Hill', 17),
        ('Richmond District', 'Bayview', 26),
        ('Union Square', 'Embarcadero', 11),
        ('Union Square', 'Richmond District', 20),
        ('Union Square', 'Financial District', 9),
        ('Union Square', 'Pacific Heights', 15),
        ('Union Square', 'Nob Hill', 9),
        ('Union Square', 'Bayview', 15),
        ('Financial District', 'Embarcadero', 4),
        ('Financial District', 'Richmond District', 21),
        ('Financial District', 'Union Square', 9),
        ('Financial District', 'Pacific Heights', 13),
        ('Financial District', 'Nob Hill', 8),
        ('Financial District', 'Bayview', 19),
        ('Pacific Heights', 'Embarcadero', 10),
        ('Pacific Heights', 'Richmond District', 12),
        ('Pacific Heights', 'Union Square', 12),
        ('Pacific Heights', 'Financial District', 13),
        ('Pacific Heights', 'Nob Hill', 8),
        ('Pacific Heights', 'Bayview', 22),
        ('Nob Hill', 'Embarcadero', 9),
        ('Nob Hill', 'Richmond District', 14),
        ('Nob Hill', 'Union Square', 7),
        ('Nob Hill', 'Financial District', 9),
        ('Nob Hill', 'Pacific Heights', 8),
        ('Nob Hill', 'Bayview', 19),
        ('Bayview', 'Embarcadero', 19),
        ('Bayview', 'Richmond District', 25),
        ('Bayview', 'Union Square', 17),
        ('Bayview', 'Financial District', 19),
        ('Bayview', 'Pacific Heights', 23),
        ('Bayview', 'Nob Hill', 20)
    ]
    
    travel_dict = {}
    for loc in locations:
        travel_dict[loc] = {}
    
    for (frm, to, time_val) in travel_list:
        travel_dict[frm][to] = time_val
    
    meetings = [
        {'name': 'start', 'location': 'Embarcadero', 'start_avail': 0, 'end_avail': 0, 'min_dur': 0, 'present': True},
        {'name': 'Kenneth', 'location': 'Richmond District', 'start_avail': 735, 'end_avail': 780, 'min_dur': 30, 'present': None},
        {'name': 'Lisa', 'location': 'Union Square', 'start_avail': 0, 'end_avail': 450, 'min_dur': 45, 'present': None},
        {'name': 'Joshua', 'location': 'Financial District', 'start_avail': 180, 'end_avail': 375, 'min_dur': 15, 'present': None},
        {'name': 'Nancy', 'location': 'Pacific Heights', 'start_avail': 0, 'end_avail': 150, 'min_dur': 90, 'present': None},
        {'name': 'Andrew', 'location': 'Nob Hill', 'start_avail': 150, 'end_avail': 675, 'min_dur': 60, 'present': None},
        {'name': 'John', 'location': 'Bayview', 'start_avail': 465, 'end_avail': 750, 'min_dur': 75, 'present': None}
    ]
    
    s = Solver()
    opt = Optimize()
    
    start_times = [Int(f'start_{i}') for i in range(7)]
    end_times = [Int(f'end_{i}') for i in range(7)]
    present_vars = [Bool(f'present_{i}') for i in range(1, 7)]
    
    s.add(start_times[0] == 0)
    s.add(end_times[0] == 0)
    
    for i in range(1, 7):
        s.add(Implies(present_vars[i-1], end_times[i] == start_times[i] + meetings[i]['min_dur']))
        s.add(Implies(present_vars[i-1], start_times[i] >= meetings[i]['start_avail']))
        s.add(Implies(present_vars[i-1], end_times[i] <= meetings[i]['end_avail']))
    
    for i in range(7):
        for j in range(i+1, 7):
            loc_i = meetings[i]['location']
            loc_j = meetings[j]['location']
            travel_ij = travel_dict[loc_i][loc_j]
            travel_ji = travel_dict[loc_j][loc_i]
            
            constraint = Or(
                end_times[i] + travel_ij <= start_times[j],
                end_times[j] + travel_ji <= start_times[i]
            )
            
            if i == 0:
                s.add(Implies(present_vars[j-1], constraint))
            else:
                s.add(Implies(And(present_vars[i-1], present_vars[j-1]), constraint))
    
    for c in s.assertions():
        opt.add(c)
    
    total_present = Sum([If(p, 1, 0) for p in present_vars])
    opt.maximize(total_present)
    
    itinerary = []
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(1, 7):
            if model.evaluate(present_vars[i-1], model_completion=True):
                start_val = model.evaluate(start_times[i], model_completion=True)
                end_val = model.evaluate(end_times[i], model_completion=True)
                if is_int_value(start_val) and is_int_value(end_val):
                    start_min = start_val.as_long()
                    end_min = end_val.as_long()
                    start_hour = 9 + start_min // 60
                    start_minute = start_min % 60
                    end_hour = 9 + end_min // 60
                    end_minute = end_min % 60
                    start_str = f"{start_hour:02d}:{start_minute:02d}"
                    end_str = f"{end_hour:02d}:{end_minute:02d}"
                    scheduled_meetings.append({
                        'person': meetings[i]['name'],
                        'start_time': start_str,
                        'end_time': end_str
                    })
        
        def time_key(t_str):
            parts = t_str.split(':')
            return (int(parts[0]), int(parts[1]))
        
        scheduled_meetings.sort(key=lambda x: time_key(x['start_time']))
        for meet in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": meet['person'],
                "start_time": meet['start_time'],
                "end_time": meet['end_time']
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()