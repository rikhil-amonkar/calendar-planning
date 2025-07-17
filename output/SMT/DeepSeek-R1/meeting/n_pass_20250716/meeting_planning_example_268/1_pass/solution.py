from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    am_pm = "AM" if hours < 12 else "PM"
    hours12 = hours % 12
    if hours12 == 0:
        hours12 = 12
    return f"{hours12}:{mins:02d}{am_pm}"

def main():
    travel_time = {
        0: {1: 10, 2: 19, 3: 11},
        1: {2: 13, 3: 18},
        2: {3: 14},
        3: {}
    }
    
    meeting_info = {
        1: {'loc': 'Alamo Square', 'start_avail': 720, 'end_avail': 975, 'min_dur': 105, 'friend': 'Timothy'},
        2: {'loc': 'Russian Hill', 'start_avail': 1005, 'end_avail': 1170, 'min_dur': 60, 'friend': 'Joseph'},
        3: {'loc': 'Presidio', 'start_avail': 1185, 'end_avail': 1260, 'min_dur': 60, 'friend': 'Mark'}
    }
    
    combinations = [
        (1, 2, 3, [0, 1, 2, 3]),
        (1, 2, [0, 1, 2]),
        (1, 3, [0, 1, 3]),
        (2, 3, [0, 2, 3]),
        (1, [0, 1]),
        (2, [0, 2]),
        (3, [0, 3])
    ]
    
    for comb in combinations:
        meetings = comb[:-1]
        sequence = comb[-1]
        s = Solver()
        
        t = Int('t')
        s.add(t >= 540)
        
        A = {}
        S = {}
        E = {}
        prev_loc = sequence[0]
        for idx, loc in enumerate(sequence[1:], start=1):
            meeting_id = meetings[idx-1] if len(meetings) < 3 else loc
            info = meeting_info[meeting_id]
            
            if idx == 1:
                A_i = t + travel_time[prev_loc][loc]
            else:
                prev_meeting_id = meetings[idx-2] if len(meetings) < 3 else sequence[idx-1]
                A_i = E[prev_meeting_id] + travel_time[prev_loc][loc]
            A[meeting_id] = A_i
            
            s.add(A_i <= info['end_avail'] - info['min_dur'])
            
            S_i = If(A_i >= info['start_avail'], A_i, info['start_avail'])
            S[meeting_id] = S_i
            E_i = S_i + info['min_dur']
            E[meeting_id] = E_i
            
            prev_loc = loc
        
        if s.check() == sat:
            m = s.model()
            schedule = []
            for meet_id in meetings:
                start_val = m.eval(S[meet_id]).as_long()
                end_val = m.eval(E[meet_id]).as_long()
                schedule.append((meet_id, start_val, end_val))
            
            print("SOLUTION:")
            for meet_id, start, end in schedule:
                friend = meeting_info[meet_id]['friend']
                location = meeting_info[meet_id]['loc']
                start_str = minutes_to_time(start)
                end_str = minutes_to_time(end)
                print(f"Meet {friend} at {location} from {start_str} to {end_str}.")
            return
    
    print("SOLUTION: No feasible schedule found.")

if __name__ == '__main__':
    main()