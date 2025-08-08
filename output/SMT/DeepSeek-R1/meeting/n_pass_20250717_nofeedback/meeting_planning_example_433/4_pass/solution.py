from z3 import *
import json

def main():
    friends = {
        'Jeffrey': {
            'location': 'Golden Gate Park',
            'min_duration': 120,
            'available_start': 11 * 60 + 15,  # 11:15
            'available_end': 14 * 60 + 30     # 14:30
        },
        'Deborah': {
            'location': 'The Castro',
            'min_duration': 90,
            'available_start': 13 * 60 + 45,  # 13:45
            'available_end': 21 * 60 + 15     # 21:15
        },
        'Margaret': {
            'location': 'Financial District',
            'min_duration': 75,
            'available_start': 16 * 60 + 30,  # 16:30
            'available_end': 20 * 60 + 15     # 20:15
        },
        'Ronald': {
            'location': 'North Beach',
            'min_duration': 45,
            'available_start': 18 * 60 + 30,  # 18:30
            'available_end': 19 * 60 + 30     # 19:30
        },
        'Emily': {
            'location': 'Richmond District',
            'min_duration': 15,
            'available_start': 19 * 60,        # 19:00
            'available_end': 21 * 60           # 21:00
        }
    }
    
    travel_times = {
        'Nob Hill': {
            'Richmond District': 14,
            'Financial District': 9,
            'North Beach': 8,
            'The Castro': 17,
            'Golden Gate Park': 17
        },
        'Richmond District': {
            'Nob Hill': 17,
            'Financial District': 22,
            'North Beach': 17,
            'The Castro': 16,
            'Golden Gate Park': 9
        },
        'Financial District': {
            'Nob Hill': 8,
            'Richmond District': 21,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'North Beach': {
            'Nob Hill': 7,
            'Richmond District': 18,
            'Financial District': 8,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Nob Hill': 16,
            'Richmond District': 16,
            'Financial District': 20,
            'North Beach': 20,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Nob Hill': 20,
            'Richmond District': 7,
            'Financial District': 26,
            'North Beach': 24,
            'The Castro': 13
        }
    }
    
    opt = Optimize()
    names = list(friends.keys())
    n = len(names)
    
    # Decision variables
    meet_vars = {name: Bool(f"meet_{name}") for name in names}
    start_vars = {name: Int(f"start_{name}") for name in names}
    end_vars = {name: Int(f"end_{name}") for name in names}
    
    # Ordering variables: before[i][j] means meeting i occurs before meeting j
    before = {}
    for i in names:
        for j in names:
            if i != j:
                before[(i, j)] = Bool(f"before_{i}_{j}")
    
    # Constraints for each meeting
    for name, data in friends.items():
        # Meeting must be within availability window
        opt.add(Implies(meet_vars[name], 
                       start_vars[name] >= data['available_start']))
        opt.add(Implies(meet_vars[name], 
                       end_vars[name] <= data['available_end']))
        opt.add(Implies(meet_vars[name],
                       end_vars[name] == start_vars[name] + data['min_duration']))
        
        # Travel time from starting location (Nob Hill)
        opt.add(Implies(meet_vars[name],
                       start_vars[name] >= 9 * 60 + travel_times['Nob Hill'][data['location']]))
    
    # Ordering and travel time constraints
    for i in names:
        for j in names:
            if i != j:
                # Mutual exclusion of ordering
                opt.add(Implies(And(meet_vars[i], meet_vars[j]),
                         before[(i, j)] != before[(j, i)]))
                
                # Travel time enforcement based on ordering
                loc_i = friends[i]['location']
                loc_j = friends[j]['location']
                travel = travel_times[loc_i][loc_j]
                opt.add(Implies(And(meet_vars[i], meet_vars[j], before[(i, j)]),
                             start_vars[j] >= end_vars[i] + travel))
    
    # Transitivity constraints
    for i in names:
        for j in names:
            for k in names:
                if i != j and i != k and j != k:
                    opt.add(Implies(And(meet_vars[i], meet_vars[j], meet_vars[k],
                                    before[(i, j)], before[(j, k)]),
                                before[(i, k)]))
    
    # At least one meeting
    opt.add(Or([meet_vars[name] for name in names]))
    
    # Optimization: maximize number of meetings, then minimize latest end time
    num_meetings = Sum([If(meet_vars[name], 1, 0) for name in names])
    max_end = Int('max_end')
    for name in names:
        opt.add(If(meet_vars[name], max_end >= end_vars[name], max_end >= 0))
    
    opt.maximize(num_meetings)
    opt.minimize(max_end)
    
    # Solve and output
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in names:
            if is_true(m.evaluate(meet_vars[name])):
                start_val = m.evaluate(start_vars[name]).as_long()
                end_val = m.evaluate(end_vars[name]).as_long()
                start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
                end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()