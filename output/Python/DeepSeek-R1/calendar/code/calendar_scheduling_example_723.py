def time_to_min(t):
    return t.hour * 60 + t.minute

def min_to_time(m):
    return f"{m // 60:02}:{m % 60:02}"

from datetime import time

# Participants' schedules
schedules = {
    'Arthur': {
        'Monday': [
            (time(11, 0), time(11, 30)),
            (time(13, 30), time(14, 0)),
            (time(15, 0), time(15, 30))
        ],
        'Wednesday': [
            (time(10, 0), time(10, 30)),
            (time(11, 0), time(11, 30)),
            (time(12, 0), time(12, 30)),
            (time(14, 0), time(14, 30)),
            (time(16, 0), time(16, 30))
        ]
    },
    'Michael': {
        'Monday': [
            (time(9, 0), time(12, 0)),
            (time(12, 30), time(13, 0)),
            (time(14, 0), time(14, 30)),
            (time(15, 0), time(17, 0))
        ],
        'Wednesday': [
            (time(10, 0), time(12, 30)),
            (time(13, 0), time(13, 30))
        ]
    }
}

def find_slot():
    days = ['Monday', 'Wednesday']
    for day in days:
        arthur_busy = schedules['Arthur'][day]
        michael_busy = schedules['Michael'][day]
        
        start_min = 9 * 60  # 9:00
        end_day = 17 * 60   # 17:00
        duration = 30
        
        for start in range(start_min, end_day - duration + 1, 15):  # Check every 15 minutes for precision
            end = start + duration
            slot_start = time(start // 60, start % 60)
            slot_end = time(end // 60, end % 60)
            
            # Check Arthur's availability
            arthur_available = True
            for (s, e) in arthur_busy:
                if not (end <= time_to_min(s) or time_to_min(e) <= start:
                    continue
                else:
                    arthur_available = False
                    break
            
            if not arthur_available:
                continue
            
            # Check Michael's availability
            michael_available = True
            for (s, e) in michael_busy:
                if not (end <= time_to_min(s) or time_to_min(e) <= start):
                    michael_available = False
                    break
            
            if michael_available:
                return (day, f"{min_to_time(start)}:{min_to_time(end)}")
    
    return None

result = find_slot()
if result:
    day, time_range = result
    print(f"{day} {time_range}")
else:
    print("No slot found")