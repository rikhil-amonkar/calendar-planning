from z3 import *
import json

def main():
    # Data for each friend
    data = [
        {'name': 'Karen', 'location': 'Nob Hill', 'window_start': 21*60+15, 'window_end': 21*60+45, 'min_duration': 30},
        {'name': 'Joseph', 'location': 'Haight-Ashbury', 'window_start': 12*60+30, 'window_end': 19*60+45, 'min_duration': 90},
        {'name': 'Sandra', 'location': 'Chinatown', 'window_start': 7*60+15, 'window_end': 19*60+15, 'min_duration': 75},
        {'name': 'Nancy', 'location': 'Marina District', 'window_start': 11*60, 'window_end': 20*60+15, 'min_duration': 105}
    ]
    
    n = len(data)
    
    # Travel times dictionary
    travel_times = {
        'Union Square': {'Nob Hill': 9, 'Haight-Ashbury': 18, 'Chinatown': 7, 'Marina District': 18},
        'Nob Hill': {'Union Square': 7, 'Haight-Ashbury': 13, 'Chinatown': 6, 'Marina District': 11},
        'Haight-Ashbury': {'Union Square': 17, 'Nob Hill': 15, 'Chinatown': 19, 'Marina District': 17},
        'Chinatown': {'Union Square': 7, 'Nob Hill': 8, 'Haight-Ashbury': 19, 'Marina District': 12},
        'Marina District': {'Union Square': 16, 'Nob Hill': 12, 'Haight-Ashbury': 16, 'Chinatown': 16}
    }
    
    # Z3 variables
    scheduled = [Bool(f'scheduled_{i}') for i in range(n)]
    start = [Real(f'start_{i}') for i in range(n)]
    end = [Real(f'end_{i}') for i in range(n)]
    
    s = Solver()
    
    # Constraints for each meeting
    for i in range(n):
        s.add(Implies(scheduled[i], start[i] >= data[i]['window_start']))
        s.add(Implies(scheduled[i], end[i] <= data[i]['window_end']))
        s.add(Implies(scheduled[i], end[i] - start[i] >= data[i]['min_duration']))
    
    # Dummy meeting at start (Union Square at 9:00 AM)
    dummy_end = 540  # 9:00 AM in minutes
    
    # Travel from start location to each meeting
    for i in range(n):
        from_loc = 'Union Square'
        to_loc = data[i]['location']
        tt = travel_times[from_loc][to_loc]
        s.add(Implies(scheduled[i], start[i] >= dummy_end + tt))
    
    # Constraints for pairs of meetings
    for i in range(n):
        for j in range(i+1, n):
            before_ij = Bool(f'before_{i}_{j}')
            # Ensure exactly one ordering if both scheduled
            s.add(Implies(And(scheduled[i], scheduled[j]), Or(before_ij, Not(before_ij))))
            # Travel time from i to j
            tt_ij = travel_times[data[i]['location']][data[j]['location']]
            # Travel time from j to i
            tt_ji = travel_times[data[j]['location']][data[i]['location']]
            # If i before j, then end_i + travel_i_j <= start_j
            s.add(Implies(And(scheduled[i], scheduled[j], before_ij), end[i] + tt_ij <= start[j]))
            # If j before i, then end_j + travel_j_i <= start_i
            s.add(Implies(And(scheduled[i], scheduled[j], Not(before_ij)), end[j] + tt_ji <= start[i]))
    
    # Find maximum number of meetings that can be scheduled
    model = None
    for k in range(n, 0, -1):
        s.push()
        s.add(AtLeast(*scheduled, k))
        if s.check() == sat:
            model = s.model()
            break
        else:
            s.pop()
    
    itinerary = []
    if model is not None:
        for i in range(n):
            if is_true(model.eval(scheduled[i])):
                start_val = model.eval(start[i])
                end_val = model.eval(end[i])
                start_min = round(float(start_val.as_string()))
                end_min = round(float(end_val.as_string()))
                hours_s = start_min // 60
                mins_s = start_min % 60
                hours_e = end_min // 60
                mins_e = end_min % 60
                start_str = f"{hours_s}:{mins_s:02d}"
                end_str = f"{hours_e}:{mins_e:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": data[i]['location'],
                    "person": data[i]['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()