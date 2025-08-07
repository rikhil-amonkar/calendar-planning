from z3 import *
import itertools
import json

def main():
    # Mapping of locations to indices: 
    # Fisherman's Wharf: 0, Bayview: 1, Golden Gate Park: 2, Nob Hill: 3, Marina District: 4, Embarcadero: 5
    # Travel time matrix: 6x6
    T = [
        [0, 26, 25, 11, 9, 8],   # from Fisherman's Wharf (0)
        [25, 0, 22, 20, 25, 19], # from Bayview (1)
        [24, 23, 0, 20, 16, 25], # from Golden Gate Park (2)
        [11, 19, 17, 0, 11, 9],  # from Nob Hill (3)
        [10, 27, 18, 12, 0, 14], # from Marina District (4)
        [6, 21, 25, 10, 12, 0]   # from Embarcadero (5)
    ]
    
    # Meetings data: each meeting has a person, location index, available start (min), available end (min), and min duration (min)
    meetings = [
        {"person": "Laura",      "loc": 3, "start_avail": 525,  "end_avail": 975,  "min_dur": 30},  # 8:45AM to 4:15PM -> 8*60+45=525, 16*60+15=975
        {"person": "Thomas",    "loc": 1, "start_avail": 930,  "end_avail": 1110, "min_dur": 120}, # 3:30PM=15*60+30=930, 6:30PM=18*60+30=1110
        {"person": "Patricia",  "loc": 5, "start_avail": 1050, "end_avail": 1320, "min_dur": 45},  # 5:30PM=17*60+30=1050, 10:00PM=22*60=1320
        {"person": "Betty",      "loc": 4, "start_avail": 1125, "end_avail": 1305, "min_dur": 45},  # 6:45PM=18*60+45=1125, 9:45PM=21*60+45=1305
        {"person": "Stephanie", "loc": 2, "start_avail": 1110, "end_avail": 1305, "min_dur": 30}   # 6:30PM=18*60+30=1110, 9:45PM=21*60+45=1305
    ]
    
    # Generate all permutations of the 5 meetings
    perms = list(itertools.permutations(range(5)))
    
    # Start from Fisherman's Wharf (index0) at 540 minutes (9:00AM)
    start_location = 0
    start_time = 540
    
    # Iterate until a feasible schedule is found
    found = False
    schedule = None
    
    for perm in perms:
        s = Solver()
        # Create integer variables for start and end times of each meeting
        S = [Int(f'S_{i}') for i in range(5)]
        E = [Int(f'E_{i}') for i in range(5)]
        
        # Add constraints for each meeting: within availability and minimum duration
        for i in range(5):
            m = meetings[i]
            s.add(S[i] >= m['start_avail'])
            s.add(S[i] <= m['end_avail'] - m['min_dur'])
            s.add(E[i] == S[i] + m['min_dur'])
            s.add(E[i] <= m['end_avail'])
        
        # Constraints for the order and travel
        first_idx = perm[0]
        travel0 = T[start_location][meetings[first_idx]['loc']]
        s.add(S[first_idx] >= start_time + travel0)
        
        # Constraints for consecutive meetings
        for idx in range(1, 5):
            prev_idx = perm[idx-1]
            curr_idx = perm[idx]
            travel_time = T[meetings[prev_idx]['loc']][meetings[curr_idx]['loc']]
            s.add(S[curr_idx] >= E[prev_idx] + travel_time)
        
        # Check if the current permutation is feasible
        if s.check() == sat:
            m = s.model()
            schedule = []
            for i in range(5):
                start_val = m.evaluate(S[i])
                end_val = m.evaluate(E[i])
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                schedule.append((meetings[i]['person'], start_min, end_min))
            found = True
            break
    
    if found:
        # Sort meetings by start time and format the itinerary
        schedule_sorted = sorted(schedule, key=lambda x: x[1])
        itinerary = []
        for person, start_min, end_min in schedule_sorted:
            start_str = f"{start_min // 60:02d}:{start_min % 60:02d}"
            end_str = f"{end_min // 60:02d}:{end_min % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": start_str,
                "end_time": end_str
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()