from z3 import *
import itertools
import json

def main():
    # Meetings data: name, location, duration, start_avail (minutes from 9:00), end_avail (minutes from 9:00)
    meetings = [
        {"name": "Helen", "loc": "NB", "dur": 15, "start_avail": 0, "end_avail": 480},
        {"name": "Kevin", "loc": "MD", "dur": 45, "start_avail": 105, "end_avail": 345},
        {"name": "Betty", "loc": "FD", "dur": 90, "start_avail": 600, "end_avail": 765},
        {"name": "Amanda", "loc": "AS", "dur": 60, "start_avail": 645, "end_avail": 720}
    ]
    
    travel_times = {
        ('PH', 'NB'): 9,
        ('PH', 'FD'): 13,
        ('PH', 'AS'): 10,
        ('PH', 'MD'): 15,
        ('NB', 'PH'): 8,
        ('NB', 'FD'): 8,
        ('NB', 'AS'): 16,
        ('NB', 'MD'): 18,
        ('FD', 'PH'): 13,
        ('FD', 'NB'): 7,
        ('FD', 'AS'): 17,
        ('FD', 'MD'): 17,
        ('AS', 'PH'): 10,
        ('AS', 'NB'): 15,
        ('AS', 'FD'): 17,
        ('AS', 'MD'): 10,
        ('MD', 'PH'): 16,
        ('MD', 'NB'): 17,
        ('MD', 'FD'): 17,
        ('MD', 'AS'): 11
    }
    
    all_meetings = [0, 1, 2, 3]  # indices for meetings
    subsets = []
    for r in range(4, 0, -1):
        for combo in itertools.combinations(all_meetings, r):
            subsets.append(combo)
    
    found = False
    itinerary = None
    
    for subset in subsets:
        n = len(subset)
        s = Solver()
        
        # Create position variables for each meeting in the subset
        pos = { i: Int(f'pos_{i}') for i in subset }
        
        # Create start time variables for each position
        S = [ Int(f'S_{j}') for j in range(n) ]
        
        # Constraints: positions are distinct and within [0, n-1]
        s.add(Distinct([pos[i] for i in subset]))
        for i in subset:
            s.add(pos[i] >= 0, pos[i] < n)
        
        # Availability constraints and first travel constraint
        for i in subset:
            for k in range(n):
                cond = (pos[i] == k)
                # Availability constraints
                s.add(Implies(cond, S[k] >= meetings[i]['start_avail']))
                s.add(Implies(cond, S[k] + meetings[i]['dur'] <= meetings[i]['end_avail']))
                # If first position, travel from PH
                if k == 0:
                    travel_key = ('PH', meetings[i]['loc'])
                    travel_time = travel_times[travel_key]
                    s.add(Implies(cond, S[k] >= travel_time))
        
        # Travel constraints between consecutive meetings
        for k in range(1, n):
            for i in subset:
                for j in subset:
                    if i != j:
                        cond = And(pos[i] == k-1, pos[j] == k)
                        travel_key = (meetings[i]['loc'], meetings[j]['loc'])
                        travel_time = travel_times[travel_key]
                        s.add(Implies(cond, S[k] >= S[k-1] + meetings[i]['dur'] + travel_time))
        
        if s.check() == sat:
            model = s.model()
            position_meetings = [None] * n
            for i in subset:
                k_val = model.eval(pos[i]).as_long()
                position_meetings[k_val] = i
            
            itinerary_list = []
            for idx in range(n):
                meeting_idx = position_meetings[idx]
                start_minutes = model.eval(S[idx]).as_long()
                hour = 9 + start_minutes // 60
                minute = start_minutes % 60
                start_time = f"{hour:02d}:{minute:02d}"
                end_minutes = start_minutes + meetings[meeting_idx]['dur']
                hour_end = 9 + end_minutes // 60
                minute_end = end_minutes % 60
                end_time = f"{hour_end:02d}:{minute_end:02d}"
                itinerary_list.append({
                    "action": "meet",
                    "person": meetings[meeting_idx]['name'],
                    "start_time": start_time,
                    "end_time": end_time
                })
            itinerary = itinerary_list
            found = True
            break
    
    if not found:
        itinerary = []
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()