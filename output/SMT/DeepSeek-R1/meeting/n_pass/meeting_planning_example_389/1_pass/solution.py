import json
from z3 import *
import itertools

def main():
    travel_times = {
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Bayview'): 26,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Mission District'): 13
    }

    friend_info = {
        'Sarah': {'location': 'Fisherman\'s Wharf', 'start': 345, 'end': 510, 'min_duration': 105},
        'Mary': {'location': 'Richmond District', 'start': 240, 'end': 615, 'min_duration': 75},
        'Helen': {'location': 'Mission District', 'start': 765, 'end': 810, 'min_duration': 30},
        'Thomas': {'location': 'Bayview', 'start': 375, 'end': 585, 'min_duration': 120}
    }

    all_friends = list(friend_info.keys())
    found = False
    solution = None

    for size in range(4, -1, -1):
        for subset in itertools.combinations(all_friends, size):
            for order in itertools.permutations(subset):
                s = Solver()
                vars_dict = {}
                for friend in subset:
                    start_var = Int(f'start_{friend}')
                    end_var = Int(f'end_{friend}')
                    vars_dict[friend] = (start_var, end_var)
                    info = friend_info[friend]
                    s.add(start_var >= info['start'])
                    s.add(end_var <= info['end'])
                    s.add(end_var - start_var >= info['min_duration'])
                    s.add(end_var >= start_var)

                if subset:
                    first_friend = order[0]
                    loc1 = friend_info[first_friend]['location']
                    tt_first = travel_times[('Haight-Ashbury', loc1)]
                    s.add(vars_dict[first_friend][0] >= tt_first)

                    for idx in range(len(order) - 1):
                        friend1 = order[idx]
                        friend2 = order[idx+1]
                        loc1 = friend_info[friend1]['location']
                        loc2 = friend_info[friend2]['location']
                        tt = travel_times[(loc1, loc2)]
                        s.add(vars_dict[friend2][0] >= vars_dict[friend1][1] + tt)

                if s.check() == sat:
                    model = s.model()
                    itinerary = []
                    for friend in subset:
                        start_val = model[vars_dict[friend][0]]
                        end_val = model[vars_dict[friend][1]]
                        start_min = start_val.as_long()
                        end_min = end_val.as_long()
                        
                        total_minutes_start = start_min
                        hour_start = 9 + total_minutes_start // 60
                        minute_start = total_minutes_start % 60
                        start_str = f"{int(hour_start):02d}:{int(minute_start):02d}"
                        
                        total_minutes_end = end_min
                        hour_end = 9 + total_minutes_end // 60
                        minute_end = total_minutes_end % 60
                        end_str = f"{int(hour_end):02d}:{int(minute_end):02d}"
                        
                        itinerary.append({
                            "action": "meet",
                            "person": friend,
                            "start_time": start_str,
                            "end_time": end_str
                        })
                    
                    itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
                    solution = {'itinerary': itinerary_sorted}
                    found = True
                    break
            if found:
                break
        if found:
            break

    if solution is None:
        solution = {'itinerary': []}

    print(json.dumps(solution))

if __name__ == "__main__":
    main()