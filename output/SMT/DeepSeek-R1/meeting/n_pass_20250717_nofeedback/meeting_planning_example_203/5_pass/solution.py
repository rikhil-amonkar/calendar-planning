from z3 import *
import itertools
import json

def main():
    travel_times = {
        ('FD', 'FW'): 10,
        ('FD', 'PH'): 13,
        ('FD', 'MD'): 17,
        ('FW', 'FD'): 11,
        ('FW', 'PH'): 12,
        ('FW', 'MD'): 22,
        ('PH', 'FD'): 13,
        ('PH', 'FW'): 13,
        ('PH', 'MD'): 15,
        ('MD', 'FD'): 17,
        ('MD', 'FW'): 22,
        ('MD', 'PH'): 16
    }
    
    friends = [
        {'name': 'Timothy', 'location': 'PH', 'start_avail': 0, 'end_avail': 270, 'min_dur': 75},
        {'name': 'David', 'location': 'FW', 'start_avail': 105, 'end_avail': 270, 'min_dur': 15},
        {'name': 'Robert', 'location': 'MD', 'start_avail': 195, 'end_avail': 645, 'min_dur': 90}
    ]
    
    found_schedule = None
    for count in [3, 2, 1]:
        if found_schedule is not None:
            break
        subsets = list(itertools.combinations(friends, count))
        for subset in subsets:
            if found_schedule is not None:
                break
            perms = list(itertools.permutations(subset))
            for order in perms:
                s = Solver()
                var_dict = {}
                for friend in subset:
                    name = friend['name']
                    var_dict[name] = Int(f's_{name}')
                
                first = order[0]
                travel_first = travel_times[('FD', first['location'])]
                s.add(var_dict[first['name']] >= travel_first)
                s.add(var_dict[first['name']] >= first['start_avail'])
                s.add(var_dict[first['name']] <= first['end_avail'] - first['min_dur'])
                
                for idx in range(1, len(order)):
                    prev = order[idx-1]
                    curr = order[idx]
                    travel_prev_curr = travel_times[(prev['location'], curr['location'])]
                    prev_end = var_dict[prev['name']] + prev['min_dur']
                    arrive_curr = prev_end + travel_prev_curr
                    s.add(var_dict[curr['name']] >= arrive_curr)
                    s.add(var_dict[curr['name']] >= curr['start_avail'])
                    s.add(var_dict[curr['name']] <= curr['end_avail'] - curr['min_dur'])
                
                # Add return constraint
                last = order[-1]
                last_end = var_dict[last['name']] + last['min_dur']
                travel_back = travel_times[(last['location'], 'FD')]
                s.add(last_end + travel_back <= 540)  # Must return by 18:00 (540 minutes)
                
                if s.check() == sat:
                    model = s.model()
                    meeting_list = []
                    for friend in subset:
                        name = friend['name']
                        start_val = model[var_dict[name]]
                        if start_val is None:
                            continue
                        start_minutes = start_val.as_long()
                        end_minutes = start_minutes + friend['min_dur']
                        start_hour = start_minutes // 60
                        start_minute = start_minutes % 60
                        end_hour = end_minutes // 60
                        end_minute = end_minutes % 60
                        start_time_str = f"{9 + start_hour:02d}:{start_minute:02d}"
                        end_time_str = f"{9 + end_hour:02d}:{end_minute:02d}"
                        meeting_list.append( (start_minutes, {
                            "action": "meet",
                            "person": name,
                            "start_time": start_time_str,
                            "end_time": end_time_str
                        }) )
                    meeting_list_sorted = sorted(meeting_list, key=lambda x: x[0])
                    itinerary = [item[1] for item in meeting_list_sorted]
                    found_schedule = itinerary
                    break
            if found_schedule is not None:
                break
        if found_schedule is not None:
            break

    if found_schedule is None:
        found_schedule = []
    
    print("SOLUTION:")
    result = {'itinerary': found_schedule}
    print(json.dumps(result))

if __name__ == "__main__":
    main()