from z3 import *
import json

def minutes_to_time(offset_minutes, base_hour=9):
    total_minutes = base_hour * 60 + offset_minutes
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

travel_dict = {
    ('FD', 'PH'): 13,
    ('FD', 'FW'): 10,
    ('FD', 'MD'): 17,
    ('PH', 'FD'): 13,
    ('PH', 'FW'): 13,
    ('PH', 'MD'): 15,
    ('FW', 'FD'): 11,
    ('FW', 'PH'): 12,
    ('FW', 'MD'): 22,
    ('MD', 'FD'): 17,
    ('MD', 'PH'): 16,
    ('MD', 'FW'): 22
}

def get_travel_time(loc1, loc2):
    return travel_dict.get((loc1, loc2), 1000000)

def schedule_meetings(meetings, start_location, start_time_offset):
    n = len(meetings)
    if n == 0:
        return []
    t = [Int(f't_{i}') for i in range(n)]
    p = [Int(f'p_{i}') for i in range(n)]
    s = Solver()
    
    for i in range(n):
        s.add(p[i] >= 0)
        s.add(p[i] < n)
    s.add(Distinct(p))
    
    for i in range(n):
        name, loc, dur, avail_start, avail_end = meetings[i]
        s.add(t[i] >= avail_start)
        s.add(t[i] + dur <= avail_end)
        s.add(t[i] >= 0)
        
    for i in range(n):
        name_i, loc_i, dur_i, avail_start_i, avail_end_i = meetings[i]
        s.add(If(p[i] == 0, t[i] >= start_time_offset + get_travel_time(start_location, loc_i), True))
        for j in range(n):
            if i == j:
                continue
            name_j, loc_j, dur_j, avail_start_j, avail_end_j = meetings[j]
            s.add(If(p[i] == p[j] + 1, t[i] >= t[j] + dur_j + get_travel_time(loc_j, loc_i), True))
            
    if s.check() == sat:
        model = s.model()
        schedule = []
        for i in range(n):
            name, loc, dur, avail_start, avail_end = meetings[i]
            start_val = model.evaluate(t[i]).as_long()
            end_val = start_val + dur
            start_str = minutes_to_time(start_val)
            end_str = minutes_to_time(end_val)
            schedule.append( (start_val, {"action": "meet", "person": name, "start_time": start_str, "end_time": end_str}) )
        schedule.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in schedule]
        return itinerary
    else:
        return None

def main():
    meetings_all = [
        ('Timothy', 'PH', 75, 0, 390),
        ('David', 'FW', 15, 105, 390),
        ('Robert', 'MD', 90, 195, 645)
    ]
    start_loc = 'FD'
    start_time_offset = 0
    
    cases = [
        [0, 1, 2],
        [0, 1],
        [0, 2],
        [1, 2],
        [0],
        [1],
        [2]
    ]
    
    result = None
    for case in cases:
        meetings_subset = [meetings_all[i] for i in case]
        result = schedule_meetings(meetings_subset, start_loc, start_time_offset)
        if result is not None:
            break
            
    if result is None:
        result = []
        
    output = {"itinerary": result}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()