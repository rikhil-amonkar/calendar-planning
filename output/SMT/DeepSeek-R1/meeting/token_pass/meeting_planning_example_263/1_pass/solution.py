from z3 import *
import json

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Financial District'): 19,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Financial District'): 5,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Fisherman\'s Wharf'): 10
    }
    
    # Meeting constraints (times in minutes since midnight)
    meetings = [
        {'name': 'Karen', 'location': 'Fisherman\'s Wharf', 'start_avail': 525, 'end_avail': 900, 'min_dur': 30},
        {'name': 'Anthony', 'location': 'Financial District', 'start_avail': 555, 'end_avail': 1290, 'min_dur': 105},
        {'name': 'Betty', 'location': 'Embarcadero', 'start_avail': 1185, 'end_avail': 1305, 'min_dur': 15}
    ]
    
    n = len(meetings)
    start_loc = 'Bayview'
    start_time = 540  # 9:00 AM in minutes since midnight
    
    # Initialize Z3 solver and variables
    opt = Optimize()
    do_meet = [Bool(f'do_meet_{i}') for i in range(n)]
    start = [Real(f'start_{i}') for i in range(n)]
    end = [Real(f'end_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]
    
    # Meeting duration and availability constraints
    for i in range(n):
        opt.add(Implies(do_meet[i], start[i] >= meetings[i]['start_avail']))
        opt.add(Implies(do_meet[i], end[i] <= meetings[i]['end_avail']))
        opt.add(Implies(do_meet[i], end[i] == start[i] + meetings[i]['min_dur']))
        opt.add(Implies(Not(do_meet[i]), order[i] == -1))
        opt.add(Implies(do_meet[i], order[i] >= 0))
        opt.add(Implies(do_meet[i], order[i] < n))
    
    # Ensure distinct orders for scheduled meetings
    opt.add(Distinct([If(do_meet[i], order[i], -1) for i in range(n)]))
    
    # First meeting must account for travel from start location
    for i in range(n):
        from_start_time = travel_times[(start_loc, meetings[i]['location'])]
        opt.add(Implies(And(do_meet[i], order[i] == 0),
                        start[i] >= start_time + from_start_time))
    
    # Travel time constraints between consecutive meetings
    for i in range(n):
        for j in range(n):
            if i != j:
                travel = travel_times[(meetings[i]['location'], meetings[j]['location'])]
                opt.add(Implies(And(do_meet[i], do_meet[j], order[j] == order[i] + 1),
                                start[j] >= end[i] + travel))
    
    # Maximize number of meetings
    total_meetings = Sum([If(do_meet[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    # Solve and output results
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled = []
        
        for i in range(n):
            if is_true(model.eval(do_meet[i])):
                o = model.eval(order[i]).as_long()
                s_val = model.eval(start[i]).as_long()
                e_val = model.eval(end[i]).as_long()
                scheduled.append((o, meetings[i]['name'], meetings[i]['location'], s_val, e_val))
        
        scheduled.sort(key=lambda x: x[0])
        
        for meeting in scheduled:
            s_hour = meeting[3] // 60
            s_min = meeting[3] % 60
            e_hour = meeting[4] // 60
            e_min = meeting[4] % 60
            itinerary.append({
                "action": "meet",
                "location": meeting[2],
                "person": meeting[1],
                "start_time": f"{s_hour}:{s_min:02d}",
                "end_time": f"{e_hour}:{e_min:02d}"
            })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()