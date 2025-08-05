from z3 import *
import itertools

def main():
    travel_dict = {
        ('Union Square', 'Golden Gate Park'): 22,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Union Square', 'Pacific Heights'): 15,
        ('Pacific Heights', 'Union Square'): 12,
        ('Union Square', 'Presidio'): 24,
        ('Presidio', 'Union Square'): 22,
        ('Union Square', 'Chinatown'): 7,
        ('Chinatown', 'Union Square'): 7,
        ('Union Square', 'The Castro'): 19,
        ('The Castro', 'Union Square'): 19,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Golden Gate Park', 'The Castro'): 13,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Pacific Heights', 'Presidio'): 11,
        ('Presidio', 'Pacific Heights'): 11,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Pacific Heights', 'The Castro'): 16,
        ('The Castro', 'Pacific Heights'): 16,
        ('Presidio', 'Chinatown'): 21,
        ('Chinatown', 'Presidio'): 19,
        ('Presidio', 'The Castro'): 21,
        ('The Castro', 'Presidio'): 20,
        ('Chinatown', 'The Castro'): 22,
        ('The Castro', 'Chinatown'): 20
    }

    friend_data = [
        {'name': 'Andrew', 'location': 'Golden Gate Park', 'start': 11*60+45, 'end': 14*60+30, 'duration': 75},
        {'name': 'Sarah', 'location': 'Pacific Heights', 'start': 16*60+15, 'end': 18*60+45, 'duration': 15},
        {'name': 'Nancy', 'location': 'Presidio', 'start': 17*60+30, 'end': 19*60+15, 'duration': 60},
        {'name': 'Rebecca', 'location': 'Chinatown', 'start': 9*60+45, 'end': 21*60+30, 'duration': 90},
        {'name': 'Robert', 'location': 'The Castro', 'start': 8*60+30, 'end': 14*60+15, 'duration': 30}
    ]

    n = len(friend_data)
    all_indices = list(range(n))
    found = False
    final_itinerary = None

    for k in range(n, 0, -1):
        for subset in itertools.combinations(all_indices, k):
            s = Solver()
            t_vars = {}
            pos_vars = {}
            for idx in subset:
                t_vars[idx] = Int(f't_{idx}')
                pos_vars[idx] = Int(f'pos_{idx}')
                s.add(pos_vars[idx] >= 0)
                s.add(pos_vars[idx] < k)
            s.add(Distinct([pos_vars[idx] for idx in subset]))
            
            for idx in subset:
                friend = friend_data[idx]
                s.add(t_vars[idx] >= friend['start'])
                s.add(t_vars[idx] + friend['duration'] <= friend['end'])
                from_union = travel_dict[('Union Square', friend['location'])]
                s.add(Implies(pos_vars[idx] == 0, t_vars[idx] >= 9*60 + from_union))
            
            for idx_i in subset:
                for idx_j in subset:
                    if idx_i == idx_j:
                        continue
                    loc_i = friend_data[idx_i]['location']
                    loc_j = friend_data[idx_j]['location']
                    travel_time = travel_dict[(loc_i, loc_j)]
                    s.add(Implies(pos_vars[idx_j] == pos_vars[idx_i] + 1,
                                  t_vars[idx_j] >= t_vars[idx_i] + friend_data[idx_i]['duration'] + travel_time))
            
            if s.check() == sat:
                m = s.model()
                schedule_entries = []
                for idx in subset:
                    pos_val = m[pos_vars[idx]].as_long()
                    start_val = m[t_vars[idx]].as_long()
                    end_val = start_val + friend_data[idx]['duration']
                    start_hour = start_val // 60
                    start_minute = start_val % 60
                    end_hour = end_val // 60
                    end_minute = end_val % 60
                    start_str = f"{start_hour:02d}:{start_minute:02d}"
                    end_str = f"{end_hour:02d}:{end_minute:02d}"
                    schedule_entries.append((pos_val, friend_data[idx]['name'], start_str, end_str))
                schedule_entries.sort(key=lambda x: x[0])
                itinerary = [{"action": "meet", "person": name, "start_time": start, "end_time": end} for (_, name, start, end) in schedule_entries]
                final_itinerary = {"itinerary": itinerary}
                found = True
                break
        if found:
            break
    
    if not found:
        final_itinerary = {"itinerary": []}
    
    print(final_itinerary)

if __name__ == "__main__":
    main()