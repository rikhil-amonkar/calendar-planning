import itertools
from z3 import *

def main():
    # Convert time to minutes from 9:00
    meetings_data = [
        {'name': 'Betty', 'location': 'Presidio', 'start_avail': 75, 'end_avail': 750, 'min_dur': 45},
        {'name': 'David', 'location': 'Richmond District', 'start_avail': 240, 'end_avail': 675, 'min_dur': 90},
        {'name': 'Barbara', 'location': 'Fisherman\'s Wharf', 'start_avail': 15, 'end_avail': 675, 'min_dur': 120}
    ]
    
    travel_times = {
        'Embarcadero': {'Presidio': 20, 'Richmond District': 21, 'Fisherman\'s Wharf': 6},
        'Presidio': {'Embarcadero': 20, 'Richmond District': 7, 'Fisherman\'s Wharf': 19},
        'Richmond District': {'Embarcadero': 19, 'Presidio': 7, 'Fisherman\'s Wharf': 18},
        'Fisherman\'s Wharf': {'Embarcadero': 8, 'Presidio': 17, 'Richmond District': 18}
    }
    
    def convert_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        hours = total_minutes // 60
        minutes_remain = total_minutes % 60
        return f"{hours}:{minutes_remain:02d}"
    
    meeting_indices = [0, 1, 2]
    found_schedule = None
    
    for subset_size in range(3, 0, -1):
        for subset in itertools.combinations(meeting_indices, subset_size):
            for order_perm in itertools.permutations(range(len(subset))):
                n = len(subset)
                S = [Int(f'S_{i}') for i in range(n)]
                E = [Int(f'E_{i}') for i in range(n)]
                solver = Solver()
                
                first_idx = order_perm[0]
                first_orig_idx = subset[first_idx]
                first_loc = meetings_data[first_orig_idx]['location']
                solver.add(S[first_idx] >= travel_times['Embarcadero'][first_loc])
                
                for i in range(n - 1):
                    from_idx = order_perm[i]
                    to_idx = order_perm[i+1]
                    from_orig = subset[from_idx]
                    to_orig = subset[to_idx]
                    from_loc = meetings_data[from_orig]['location']
                    to_loc = meetings_data[to_orig]['location']
                    travel_time = travel_times[from_loc][to_loc]
                    solver.add(S[to_idx] >= E[from_idx] + travel_time)
                
                for i in range(n):
                    orig_idx = subset[i]
                    solver.add(S[i] >= meetings_data[orig_idx]['start_avail'])
                    solver.add(E[i] <= meetings_data[orig_idx]['end_avail'])
                    solver.add(E[i] - S[i] >= meetings_data[orig_idx]['min_dur'])
                
                if solver.check() == sat:
                    model = solver.model()
                    schedule = []
                    for i in range(n):
                        orig_idx = subset[i]
                        s_val = model.evaluate(S[i])
                        e_val = model.evaluate(E[i])
                        if is_int_value(s_val) and is_int_value(e_val):
                            s_int = s_val.as_long()
                            e_int = e_val.as_long()
                            start_str = convert_to_time(s_int)
                            end_str = convert_to_time(e_int)
                            meeting = {
                                'action': 'meet',
                                'location': meetings_data[orig_idx]['location'],
                                'person': meetings_data[orig_idx]['name'],
                                'start_time': start_str,
                                'end_time': end_str
                            }
                            schedule.append(meeting)
                    schedule.sort(key=lambda x: x['start_time'])
                    found_schedule = schedule
                    break
            if found_schedule:
                break
        if found_schedule:
            break
    
    if found_schedule is None:
        found_schedule = []
    
    output = {"itinerary": found_schedule}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    import json
    main()