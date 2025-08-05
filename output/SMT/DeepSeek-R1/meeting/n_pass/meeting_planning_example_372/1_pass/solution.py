from z3 import *
import itertools

def main():
    locations = {
        "Margaret": "Russian Hill",
        "Daniel": "Golden Gate Park",
        "Charles": "Alamo Square",
        "Stephanie": "Mission District"
    }
    
    travel_times = {
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Mission District"): 24,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Mission District"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Mission District"): 16,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Mission District"): 17,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Golden Gate Park"): 17
    }

    all_friends = ["Margaret", "Daniel", "Charles", "Stephanie"]
    model = None
    best_schedule = None
    best_friends = None

    for k in range(4, 0, -1):
        found = False
        for subset in itertools.combinations(all_friends, k):
            result = schedule_subset(list(subset), locations, travel_times)
            if result is not None:
                model = result
                best_friends = list(subset)
                found = True
                break
        if found:
            break

    if model is None:
        print('{"itinerary": []}')
        return

    start_vars = {}
    end_vars = {}
    for friend in best_friends:
        start_vars[friend] = Int(f'start_{friend}')
        end_vars[friend] = Int(f'end_{friend}')

    meetings = []
    for friend in best_friends:
        start_val = model.eval(start_vars[friend]).as_long()
        end_val = model.eval(end_vars[friend]).as_long()
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        meetings.append({
            "action": "meet",
            "person": friend,
            "start_time": start_str,
            "end_time": end_str
        })

    meetings_sorted = sorted(meetings, key=lambda x: x['start_time'])
    print('SOLUTION:')
    print(f'{{"itinerary": {meetings_sorted}}}')

def schedule_subset(subset, locations, travel_times):
    s = Solver()
    k = len(subset)
    start_vars = {friend: Int(f'start_{friend}') for friend in subset}
    end_vars = {friend: Int(f'end_{friend}') for friend in subset}
    pos_vars = {friend: Int(f'pos_{friend}') for friend in subset}
    
    for friend in subset:
        s.add(pos_vars[friend] >= 0)
        s.add(pos_vars[friend] < k)
        
    s.add(Distinct([pos_vars[friend] for friend in subset]))
    
    for friend in subset:
        if friend == "Margaret":
            s.add(start_vars[friend] >= 24)
            s.add(end_vars[friend] <= 420)
            s.add(end_vars[friend] - start_vars[friend] >= 30)
        elif friend == "Daniel":
            s.add(start_vars[friend] >= 11)
            s.add(end_vars[friend] <= 270)
            s.add(end_vars[friend] - start_vars[friend] >= 15)
        elif friend == "Charles":
            s.add(start_vars[friend] >= 540)
            s.add(end_vars[friend] <= 705)
            s.add(end_vars[friend] - start_vars[friend] >= 90)
        elif friend == "Stephanie":
            s.add(start_vars[friend] >= 690)
            s.add(end_vars[friend] <= 780)
            s.add(end_vars[friend] - start_vars[friend] >= 90)
    
    for friend in subset:
        from_loc = "Sunset District"
        to_loc = locations[friend]
        travel_time = travel_times[(from_loc, to_loc)]
        s.add(Implies(pos_vars[friend] == 0, start_vars[friend] >= travel_time))
    
    for i in subset:
        for j in subset:
            if i == j:
                continue
            from_loc = locations[i]
            to_loc = locations[j]
            travel_time = travel_times[(from_loc, to_loc)]
            s.add(Implies(pos_vars[j] == pos_vars[i] + 1, end_vars[i] + travel_time <= start_vars[j]))
    
    if s.check() == sat:
        return s.model()
    else:
        return None

if __name__ == '__main__':
    main()