from itertools import permutations
from z3 import *

def min_to_time(total_minutes):
    total_hours = total_minutes // 60
    minutes = total_minutes % 60
    hours = 9 + total_hours
    return f"{hours:02d}:{minutes:02d}"

def main():
    names = ['Carol', 'Karen', 'Rebecca']
    locs = ['S', 'B', 'M']  # S: Sunset, B: Bayview, M: Mission
    windows = [
        (75, 165),   # Carol: 10:15 AM (75 min from 9:00) to 11:45 AM (165 min)
        (225, 360),  # Karen: 12:45 PM (225 min) to 3:00 PM (360 min)
        (150, 675)   # Rebecca: 11:30 AM (150 min) to 8:15 PM (675 min)
    ]
    durations = [30, 120, 120]
    
    travel_times = {
        ('US', 'S'): 26,
        ('US', 'B'): 15,
        ('US', 'M'): 14,
        ('S', 'US'): 30,
        ('S', 'B'): 22,
        ('S', 'M'): 24,
        ('B', 'US'): 17,
        ('B', 'S'): 23,
        ('B', 'M'): 13,
        ('M', 'US'): 15,
        ('M', 'S'): 24,
        ('M', 'B'): 15
    }
    
    perms = list(permutations([0, 1, 2]))
    found = False
    result_meetings = None
    
    for perm in perms:
        s = Solver()
        start0 = Int(f'start0_{perm}')
        start1 = Int(f'start1_{perm}')
        start2 = Int(f'start2_{perm}')
        starts = [start0, start1, start2]
        
        loc0 = locs[perm[0]]
        loc1 = locs[perm[1]]
        loc2 = locs[perm[2]]
        
        s.add(start0 >= travel_times[('US', loc0)])
        s.add(start1 >= start0 + durations[perm[0]] + travel_times[(loc0, loc1)])
        s.add(start2 >= start1 + durations[perm[1]] + travel_times[(loc1, loc2)])
        
        for i in range(3):
            idx = perm[i]
            s.add(starts[i] >= windows[idx][0])
            s.add(starts[i] + durations[idx] <= windows[idx][1])
        
        if s.check() == sat:
            m = s.model()
            start_vals = [m[starts[i]].as_long() for i in range(3)]
            meetings = []
            for i in range(3):
                idx = perm[i]
                start_min = start_vals[i]
                end_min = start_min + durations[idx]
                meetings.append((start_min, names[idx], start_min, end_min))
            meetings_sorted = sorted(meetings, key=lambda x: x[0])
            result_meetings = meetings_sorted
            found = True
            break
    
    if not found:
        print("No valid schedule found.")
        return
    
    itinerary = []
    for meeting in result_meetings:
        _, person, start_min, end_min = meeting
        start_time = min_to_time(start_min)
        end_time = min_to_time(end_min)
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": start_time,
            "end_time": end_time
        })
    
    import json
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()