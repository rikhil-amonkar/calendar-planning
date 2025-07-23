from z3 import *
import json

def main():
    friends_data = [
        {'name': 'Michelle', 'location': 'Golden Gate Park', 
         'window_start': 660, 'window_end': 720, 'min_duration': 15},
        {'name': 'Emily', 'location': 'Fisherman\'s Wharf', 
         'window_start': 435, 'window_end': 600, 'min_duration': 30},
        {'name': 'Mark', 'location': 'Marina District', 
         'window_start': 555, 'window_end': 645, 'min_duration': 75},
        {'name': 'Barbara', 'location': 'Alamo Square', 
         'window_start': 480, 'window_end': 600, 'min_duration': 120},
        {'name': 'Laura', 'location': 'Sunset District', 
         'window_start': 600, 'window_end': 735, 'min_duration': 75},
        {'name': 'Mary', 'location': 'Nob Hill', 
         'window_start': 510, 'window_end': 600, 'min_duration': 45},
        {'name': 'Helen', 'location': 'North Beach', 
         'window_start': 120, 'window_end': 195, 'min_duration': 45}
    ]
    
    travel_dict = {
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,

        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "North Beach"): 23,

        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,

        ("Marina District", "Presidio"): 10,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "North Beach"): 11,

        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,

        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "North Beach"): 28,

        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "North Beach"): 8,

        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Nob Hill"): 7
    }

    s = Solver()
    n = len(friends_data)
    met = [Bool(f'met_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]
    
    for i in range(n):
        f = friends_data[i]
        s.add(Implies(met[i], start[i] >= f['window_start']))
        s.add(Implies(met[i], end[i] <= f['window_end']))
        s.add(Implies(met[i], end[i] - start[i] >= f['min_duration']))
        s.add(Implies(met[i], And(order[i] >= 0, order[i] < n)))
        
    for i in range(n):
        for j in range(i+1, n):
            s.add(Implies(And(met[i], met[j]), order[i] != order[j]))
            
    for i in range(n):
        from_loc = "Presidio"
        to_loc = friends_data[i]['location']
        tt = travel_dict.get((from_loc, to_loc))
        if tt is None:
            tt = 1000
        s.add(Implies(met[i], start[i] >= tt))
        
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            loc_i = friends_data[i]['location']
            loc_j = friends_data[j]['location']
            tt = travel_dict.get((loc_i, loc_j))
            if tt is None:
                tt = 1000
            s.add(Implies(And(met[i], met[j], order[i] < order[j]), 
                          start[j] >= end[i] + tt))
    
    num_met = Sum([If(met[i], 1, 0) for i in range(n)])
    s.maximize(num_met)
    
    if s.check() == sat:
        model = s.model()
        itinerary_unsorted = []
        order_vals = []
        for i in range(n):
            if is_true(model[met[i]]):
                start_val = model[start[i]].as_long()
                end_val = model[end[i]].as_long()
                order_val = model[order[i]].as_long()
                total_minutes_start = start_val
                total_minutes_end = end_val
                hour_start = total_minutes_start // 60 + 9
                min_start = total_minutes_start % 60
                hour_end = total_minutes_end // 60 + 9
                min_end = total_minutes_end % 60
                start_str = f"{hour_start}:{min_start:02d}"
                end_str = f"{hour_end}:{min_end:02d}"
                itinerary_unsorted.append({
                    'action': 'meet',
                    'person': friends_data[i]['name'],
                    'start_time': start_str,
                    'end_time': end_str,
                    'order': order_val
                })
                order_vals.append(order_val)
        
        itinerary_sorted = sorted(itinerary_unsorted, key=lambda x: x['order'])
        itinerary_final = [{'action': x['action'], 'person': x['person'], 
                           'start_time': x['start_time'], 'end_time': x['end_time']} 
                          for x in itinerary_sorted]
        print("SOLUTION:")
        print(json.dumps({'itinerary': itinerary_final}))
    else:
        print("SOLUTION:")
        print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()