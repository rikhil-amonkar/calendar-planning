from datetime import time

def find_meeting_time(terry_busy, frances_busy, days, duration_minutes=30):
    work_start = time(9, 0)
    work_end = time(17, 0)
    
    for day in days:
        if day == "Tuesday":
            continue  # Frances prefers to avoid meetings on Tuesday
            
        # Get all busy intervals for Terry and Frances on the current day
        terry_day = terry_busy.get(day, [])
        frances_day = frances_busy.get(day, [])
        
        # Combine and sort all busy intervals
        all_busy = terry_day + frances_day
        all_busy.sort()
        
        # Check gaps between busy intervals
        prev_end = work_start
        for busy_start, busy_end in all_busy:
            if busy_start > prev_end:
                gap_duration = (busy_start.hour * 60 + busy_start.minute) - (prev_end.hour * 60 + prev_end.minute)
                if gap_duration >= duration_minutes:
                    return day, prev_end, time(prev_end.hour, prev_end.minute + duration_minutes)
            prev_end = max(prev_end, busy_end)
        
        # Check gap after last busy interval
        if prev_end < work_end:
            gap_duration = (work_end.hour * 60 + work_end.minute) - (prev_end.hour * 60 + prev_end.minute)
            if gap_duration >= duration_minutes:
                return day, prev_end, time(prev_end.hour, prev_end.minute + duration_minutes)
    
    return None

def main():
    terry_busy = {
        "Monday": [(time(10, 30), time(11, 0)), (time(12, 30), time(14, 0)), (time(15, 0), time(17, 0))],
        "Tuesday": [(time(9, 30), time(10, 0)), (time(10, 30), time(11, 0)), (time(14, 0), time(14, 30)), (time(16, 0), time(16, 30))],
        "Wednesday": [(time(9, 30), time(10, 30)), (time(11, 0), time(12, 0)), (time(13, 0), time(13, 30)), (time(15, 0), time(16, 0)), (time(16, 30), time(17, 0))],
        "Thursday": [(time(9, 30), time(10, 0)), (time(12, 0), time(12, 30)), (time(13, 0), time(14, 30)), (time(16, 0), time(16, 30))],
        "Friday": [(time(9, 0), time(11, 30)), (time(12, 0), time(12, 30)), (time(13, 30), time(16, 0)), (time(16, 30), time(17, 0))]
    }
    
    frances_busy = {
        "Monday": [(time(9, 30), time(11, 0)), (time(11, 30), time(13, 0)), (time(14, 0), time(14, 30)), (time(15, 0), time(16, 0))],
        "Tuesday": [(time(9, 0), time(9, 30)), (time(10, 0), time(10, 30)), (time(11, 0), time(12, 0)), (time(13, 0), time(14, 30)), (time(15, 30), time(16, 30))],
        "Wednesday": [(time(9, 30), time(10, 0)), (time(10, 30), time(11, 0)), (time(11, 30), time(16, 0)), (time(16, 30), time(17, 0))],
        "Thursday": [(time(11, 0), time(12, 30)), (time(14, 30), time(17, 0))],
        "Friday": [(time(9, 30), time(10, 30)), (time(11, 0), time(12, 30)), (time(13, 0), time(16, 0)), (time(16, 30), time(17, 0))]
    }
    
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    result = find_meeting_time(terry_busy, frances_busy, days)
    
    if result:
        day, start, end = result
        print(f"{day}, {start.hour:02d}:{start.minute:02d}:{end.hour:02d}:{end.minute:02d}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()