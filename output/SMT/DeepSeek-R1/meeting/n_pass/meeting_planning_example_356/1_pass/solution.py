import z3
from itertools import combinations, permutations
import json

def main():
    travel_times = {
        'Bayview': {'North Beach': 21, 'Presidio': 31, 'Haight-Ashbury': 19, 'Union Square': 17},
        'North Beach': {'Bayview': 22, 'Presidio': 17, 'Haight-Ashbury': 18, 'Union Square': 7},
        'Presidio': {'Bayview': 31, 'North Beach': 18, 'Haight-Ashbury': 15, 'Union Square': 22},
        'Haight-Ashbury': {'Bayview': 18, 'North Beach': 19, 'Presidio': 15, 'Union Square': 17},
        'Union Square': {'Bayview': 15, 'North Beach': 10, 'Presidio': 24, 'Haight-Ashbury': 18}
    }
    
    friends_info = [
        {'name': 'Barbara', 'loc': 'North Beach', 'start_avail': 13*60+45, 'end_avail': 20*60+15, 'duration': 60},
        {'name': 'Margaret', 'loc': 'Presidio', 'start_avail': 10*60+15, 'end_avail': 15*60+15, 'duration': 30},
        {'name': 'Kevin', 'loc': 'Haight-Ashbury', 'start_avail': 20*60, 'end_avail': 20*60+45, 'duration': 30},
        {'name': 'Kimberly', 'loc': 'Union Square', 'start_avail': 7*60+45, 'end_avail': 16*60+45, 'duration': 30}
    ]
    
    found = False
    solution_itinerary = None
    
    for n in range(4, 0, -1):
        if found:
            break
        for subset in combinations(friends_info, n):
            if found:
                break
            for order in permutations(subset):
                if found:
                    break
                s = z3.Solver()
                current_loc = 'Bayview'
                current_time = 540  # 9:00 AM
                start_vars = []
                for idx, friend in enumerate(order):
                    start_var = z3.Int(f'start_{idx}')
                    start_vars.append(start_var)
                    tt = travel_times[current_loc][friend['loc']]
                    s.add(start_var >= current_time + tt)
                    s.add(start_var >= friend['start_avail'])
                    s.add(start_var + friend['duration'] <= friend['end_avail'])
                    current_loc = friend['loc']
                    current_time = start_var + friend['duration']
                if s.check() == z3.sat:
                    m = s.model()
                    itinerary = []
                    for idx, friend in enumerate(order):
                        start_val = m[start_vars[idx]].as_long()
                        end_val = start_val + friend['duration']
                        start_str = f"{start_val // 60:02d}:{start_val % 60:02d}"
                        end_str = f"{end_val // 60:02d}:{end_val % 60:02d}"
                        itinerary.append({
                            "action": "meet",
                            "person": friend['name'],
                            "start_time": start_str,
                            "end_time": end_str
                        })
                    solution_itinerary = itinerary
                    found = True
                    break
    
    print("SOLUTION:")
    if solution_itinerary is not None:
        print(json.dumps({"itinerary": solution_itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()