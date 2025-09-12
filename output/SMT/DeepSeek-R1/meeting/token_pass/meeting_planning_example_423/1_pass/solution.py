from z3 import *
import json

def main():
    travel_times = {
        'Presidio': {
            'Richmond District': 7,
            'North Beach': 18,
            'Financial District': 23,
            'Golden Gate Park': 12,
            'Union Square': 22
        },
        'Richmond District': {
            'Presidio': 7,
            'North Beach': 17,
            'Financial District': 22,
            'Golden Gate Park': 9,
            'Union Square': 21
        },
        'North Beach': {
            'Presidio': 17,
            'Richmond District': 18,
            'Financial District': 8,
            'Golden Gate Park': 22,
            'Union Square': 7
        },
        'Financial District': {
            'Presidio': 22,
            'Richmond District': 21,
            'North Beach': 7,
            'Golden Gate Park': 23,
            'Union Square': 9
        },
        'Golden Gate Park': {
            'Presidio': 11,
            'Richmond District': 7,
            'North Beach': 24,
            'Financial District': 26,
            'Union Square': 22
        },
        'Union Square': {
            'Presidio': 24,
            'Richmond District': 20,
            'North Beach': 10,
            'Financial District': 9,
            'Golden Gate Park': 22
        }
    }

    meetings = [
        {'name': 'Jason', 'location': 'Richmond District', 'start_avail': 240, 'end_avail': 705, 'min_dur': 90},
        {'name': 'Melissa', 'location': 'North Beach', 'start_avail': 585, 'end_avail': 675, 'min_dur': 45},
        {'name': 'Brian', 'location': 'Financial District', 'start_avail': 45, 'end_avail': 765, 'min_dur': 15},
        {'name': 'Elizabeth', 'location': 'Golden Gate Park', 'start_avail': 0, 'end_avail': 750, 'min_dur': 105},
        {'name': 'Laura', 'location': 'Union Square', 'start_avail': 315, 'end_avail': 630, 'min_dur': 75}
    ]

    num_meetings = len(meetings)
    start = [Int(f'start_{i}') for i in range(num_meetings)]
    end = [Int(f'end_{i}') for i in range(num_meetings)]
    included = [Bool(f'included_{i}') for i in range(num_meetings)]

    opt = Optimize()
    
    for i in range(num_meetings):
        m = meetings[i]
        opt.add(Implies(included[i], start[i] >= m['start_avail']))
        opt.add(Implies(included[i], end[i] <= m['end_avail']))
        opt.add(Implies(included[i], end[i] - start[i] >= m['min_dur']))
        opt.add(Implies(included[i], start[i] >= travel_times['Presidio'][m['location']]))
    
    for i in range(num_meetings):
        for j in range(i + 1, num_meetings):
            loc_i = meetings[i]['location']
            loc_j = meetings[j]['location']
            time_ij = travel_times[loc_i][loc_j]
            time_ji = travel_times[loc_j][loc_i]
            opt.add(Implies(And(included[i], included[j]),
                            Or(end[i] + time_ij <= start[j],
                               end[j] + time_ji <= start[i])))
    
    total_included = Sum([If(included[i], 1, 0) for i in range(num_meetings)])
    opt.maximize(total_included)
    
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for i in range(num_meetings):
            if is_true(model.eval(included[i])):
                s_val = model.eval(start[i]).as_long()
                e_val = model.eval(end[i]).as_long()
                start_hour = (s_val // 60) + 9
                start_min = s_val % 60
                end_hour = (e_val // 60) + 9
                end_min = e_val % 60
                start_str = f"{start_hour}:{start_min:02d}"
                end_str = f"{end_hour}:{end_min:02d}"
                schedule.append({
                    'start_val': s_val,
                    'end_val': e_val,
                    'name': meetings[i]['name'],
                    'location': meetings[i]['location'],
                    'start_str': start_str,
                    'end_str': end_str
                })
        
        schedule.sort(key=lambda x: x['start_val'])
        itinerary = [{
            'action': 'meet',
            'location': item['location'],
            'person': item['name'],
            'start_time': item['start_str'],
            'end_time': item['end_str']
        } for item in schedule]
        
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()