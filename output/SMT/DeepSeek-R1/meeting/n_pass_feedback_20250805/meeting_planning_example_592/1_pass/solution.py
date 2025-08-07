from z3 import *
import json

def main():
    # Define travel times between locations
    travel_times = {
        'North Beach': {
            'Pacific Heights': 8,
            'Chinatown': 6,
            'Union Square': 7,
            'Mission District': 18,
            'Golden Gate Park': 22,
            'Nob Hill': 7
        },
        'Pacific Heights': {
            'North Beach': 9,
            'Chinatown': 11,
            'Union Square': 12,
            'Mission District': 15,
            'Golden Gate Park': 15,
            'Nob Hill': 8
        },
        'Chinatown': {
            'North Beach': 3,
            'Pacific Heights': 10,
            'Union Square': 7,
            'Mission District': 18,
            'Golden Gate Park': 23,
            'Nob Hill': 8
        },
        'Union Square': {
            'North Beach': 10,
            'Pacific Heights': 15,
            'Chinatown': 7,
            'Mission District': 14,
            'Golden Gate Park': 22,
            'Nob Hill': 9
        },
        'Mission District': {
            'North Beach': 17,
            'Pacific Heights': 16,
            'Chinatown': 16,
            'Union Square': 15,
            'Golden Gate Park': 17,
            'Nob Hill': 12
        },
        'Golden Gate Park': {
            'North Beach': 24,
            'Pacific Heights': 16,
            'Chinatown': 23,
            'Union Square': 22,
            'Mission District': 17,
            'Nob Hill': 20
        },
        'Nob Hill': {
            'North Beach': 8,
            'Pacific Heights': 8,
            'Chinatown': 6,
            'Union Square': 7,
            'Mission District': 13,
            'Golden Gate Park': 17
        }
    }
    
    # Define friends' details: availability and duration
    friends = [
        {'name': 'James', 'loc': 'Pacific Heights', 'start_avail': 660, 'end_avail': 780, 'min_duration': 120},
        {'name': 'Robert', 'loc': 'Chinatown', 'start_avail': 195, 'end_avail': 465, 'min_duration': 90},
        {'name': 'Jeffrey', 'loc': 'Union Square', 'start_avail': 30, 'end_avail': 390, 'min_duration': 120},
        {'name': 'Carol', 'loc': 'Mission District', 'start_avail': 555, 'end_avail': 735, 'min_duration': 15},
        {'name': 'Mark', 'loc': 'Golden Gate Park', 'start_avail': 150, 'end_avail': 525, 'min_duration': 15},
        {'name': 'Sandra', 'loc': 'Nob Hill', 'start_avail': 0, 'end_avail': 390, 'min_duration': 15}
    ]
    
    # Initialize Z3 variables
    num_slots = 6
    who = [Int(f'who_{i}') for i in range(num_slots)]
    start = [Int(f'start_{i}') for i in range(num_slots)]
    end = [Int(f'end_{i}') for i in range(num_slots)]
    
    s = Solver()
    
    # Constraints: who[i] is between 0 and 6 (0 means no meeting)
    for i in range(num_slots):
        s.add(Or(And(who[i] >= 1, who[i] <= 6), who[i] == 0)
    
    # If a slot is empty, subsequent slots must be empty
    for i in range(num_slots - 1):
        s.add(If(who[i] == 0, who[i + 1] == 0, True))
    
    # Each friend is met at most once
    for fid in range(1, 7):
        s.add(Sum([If(who[i] == fid, 1, 0) for i in range(num_slots)]) <= 1)
    
    # Constraints for the first slot
    for fid in range(1, 7):
        friend = friends[fid - 1]
        tt = travel_times['North Beach'][friend['loc']]
        s.add(If(who[0] == fid,
                 And(start[0] >= tt,
                     start[0] >= friend['start_avail'],
                     end[0] == start[0] + friend['min_duration'],
                     end[0] <= friend['end_avail']),
                 True))
    
    # Constraints for subsequent slots
    for slot in range(1, num_slots):
        for fid_prev in range(1, 7):
            for fid_curr in range(1, 7):
                if fid_prev == fid_curr:
                    continue
                friend_prev = friends[fid_prev - 1]
                friend_curr = friends[fid_curr - 1]
                tt = travel_times[friend_prev['loc']][friend_curr['loc']]
                cond = And(who[slot - 1] == fid_prev, who[slot] == fid_curr)
                s.add(If(cond,
                         And(start[slot] >= end[slot - 1] + tt,
                             start[slot] >= friend_curr['start_avail'],
                             end[slot] == start[slot] + friend_curr['min_duration'],
                             end[slot] <= friend_curr['end_avail']),
                         True))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(who[i] != 0, 1, 0) for i in range(num_slots)])
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(total_meetings)
    
    itinerary = []
    if opt.check() == sat:
        m = opt.model()
        for i in range(num_slots):
            w_val = m.eval(who[i])
            if w_val.as_long() == 0:
                break
            fid = w_val.as_long()
            friend = friends[fid - 1]
            s_val = m.eval(start[i]).as_long()
            e_val = m.eval(end[i]).as_long()
            # Convert minutes to time string (from 9:00 AM base)
            total_minutes_start = s_val
            hours_start = total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            abs_hour_start = 9 + hours_start
            abs_minute_start = minutes_start
            start_time = f"{abs_hour_start:02d}:{abs_minute_start:02d}"
            
            total_minutes_end = e_val
            hours_end = total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            abs_hour_end = 9 + hours_end
            abs_minute_end = minutes_end
            end_time = f"{abs_hour_end:02d}:{abs_minute_end:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_time,
                "end_time": end_time
            })
        print('SOLUTION:')
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()