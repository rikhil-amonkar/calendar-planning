from z3 import *
import itertools

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    minutes_part = total_minutes % 60
    return f"{hours:02d}:{minutes_part:02d}"

def main():
    travel_time = [
        [0, 9, 18, 7, 18],
        [7, 0, 13, 6, 11],
        [17, 15, 0, 19, 17],
        [7, 8, 19, 0, 12],
        [16, 12, 16, 16, 0]
    ]
    
    meetings_db = [
        {   # Sandra
            'name': 'Sandra',
            'duration': 75,
            'location': 3,
            'min_start': 0,
            'max_start': 540   # 615-75
        },
        {   # Joseph
            'name': 'Joseph',
            'duration': 90,
            'location': 2,
            'min_start': 210,  # 12:30 PM is 210 minutes from 9:00 AM
            'max_start': 555    # 645-90
        },
        {   # Nancy
            'name': 'Nancy',
            'duration': 105,
            'location': 4,
            'min_start': 120,   # 11:00 AM is 120 minutes from 9:00 AM
            'max_start': 570     # 675-105
        }
    ]
    
    karen_meeting = {
        'action': 'meet',
        'person': 'Karen',
        'start_time': '21:15',
        'end_time': '21:45'
    }
    
    def solve_for_set(meeting_indices):
        meetings_included = [meetings_db[i] for i in meeting_indices]
        M = len(meetings_included)
        if M == 0:
            return [karen_meeting]
        
        s = [Int(f's_{i}') for i in range(M)]
        order = [Int(f'order_{i}') for i in range(M)]
        solver = Solver()
        
        solver.add(Distinct(order))
        for i in range(M):
            solver.add(order[i] >= 0, order[i] < M)
        
        locs = [meet['location'] for meet in meetings_included]
        durs = [meet['duration'] for meet in meetings_included]
        min_starts = [meet['min_start'] for meet in meetings_included]
        max_starts = [meet['max_start'] for meet in meetings_included]
        
        T_array = Array('T', IntSort(), IntSort())
        for i_val in range(5):
            for j_val in range(5):
                idx_val = i_val * 5 + j_val
                T_array = Store(T_array, idx_val, travel_time[i_val][j_val])
        
        def get_travel_time(from_loc, to_loc):
            return T_array[from_loc * 5 + to_loc]
        
        travel_start = []
        travel_duration = []
        travel_loc = []
        for k in range(M):
            options_s = []
            options_dur = []
            options_loc = []
            for idx in range(M):
                options_s.append(s[idx])
                options_dur.append(durs[idx])
                options_loc.append(locs[idx])
            travel_start_k = If(order[k] == 0, options_s[0], 
                               If(order[k] == 1, options_s[1] if M>1 else options_s[0],
                               If(order[k] == 2, options_s[2] if M>2 else options_s[0], 0)))
            travel_duration_k = If(order[k] == 0, options_dur[0],
                                  If(order[k] == 1, options_dur[1] if M>1 else options_dur[0],
                                  If(order[k] == 2, options_dur[2] if M>2 else options_dur[0], 0)))
            travel_loc_k = If(order[k] == 0, options_loc[0],
                             If(order[k] == 1, options_loc[1] if M>1 else options_loc[0],
                             If(order[k] == 2, options_loc[2] if M>2 else options_loc[0], 0)))
            travel_start.append(travel_start_k)
            travel_duration.append(travel_duration_k)
            travel_loc.append(travel_loc_k)
        
        solver.add(travel_start[0] >= get_travel_time(0, travel_loc[0]))
        
        for k in range(1, M):
            solver.add(travel_start[k] >= travel_start[k-1] + travel_duration[k-1] + get_travel_time(travel_loc[k-1], travel_loc[k]))
        
        solver.add(travel_start[M-1] + travel_duration[M-1] + get_travel_time(travel_loc[M-1], 1) <= 735)
        
        for i in range(M):
            solver.add(s[i] >= min_starts[i], s[i] <= max_starts[i])
        
        if solver.check() == sat:
            model = solver.model()
            start_times = []
            for i in range(M):
                start_val = model.evaluate(s[i])
                start_times.append(start_val.as_long())
            events = []
            for i in range(M):
                meet_info = meetings_included[i]
                start = start_times[i]
                end = start + meet_info['duration']
                events.append({
                    'action': 'meet',
                    'person': meet_info['name'],
                    'start_time': minutes_to_time(start),
                    'end_time': minutes_to_time(end)
                })
            events.append(karen_meeting)
            events_sorted = sorted(events, key=lambda x: (x['start_time'], x['end_time']))
            return events_sorted
        else:
            return None
    
    sets_to_try = [
        [0, 1, 2],
        [0, 1], [0, 2], [1, 2],
        [0], [1], [2],
        []
    ]
    
    result_events = None
    for s in sets_to_try:
        res = solve_for_set(s)
        if res is not None:
            result_events = res
            break
    
    output = {"itinerary": result_events}
    print('SOLUTION:')
    print(output)

if __name__ == "__main__":
    main()