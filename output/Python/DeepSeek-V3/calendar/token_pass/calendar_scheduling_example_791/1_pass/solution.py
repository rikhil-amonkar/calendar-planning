from datetime import datetime, timedelta

def time_to_minutes(t):
    # t is string "HH:MM"
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    days = ["Monday", "Tuesday", "Wednesday"]
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 30
    
    # Nicole's busy times in minutes from 0:00, but we'll convert from given times
    nicole_busy = {
        "Monday": ["9:00-9:30", "13:00-13:30", "14:30-15:30"],
        "Tuesday": ["9:00-9:30", "11:30-13:30", "14:30-15:30"],
        "Wednesday": ["10:00-11:00", "12:30-15:00", "16:00-17:00"]
    }
    
    ruth_busy = {
        "Monday": ["9:00-17:00"],
        "Tuesday": ["9:00-17:00"],
        "Wednesday": ["9:00-10:30", "11:00-11:30", "12:00-12:30", "13:30-15:30", "16:00-16:30"]
    }
    
    # Ruth doesn't want to meet on Wednesday after 13:30
    ruth_wed_cutoff = time_to_minutes("13:30")
    
    for day in days:
        # Convert busy times to minutes since midnight for easier overlap
        # But simpler: generate free slots for each person within work hours
        def busy_to_free(busy_list, day_name):
            busy_times = []
            for slot in busy_list[day_name]:
                s, e = slot.split('-')
                busy_times.append((time_to_minutes(s), time_to_minutes(e)))
            # Sort by start time
            busy_times.sort()
            free = []
            prev_end = work_start
            for start, end in busy_times:
                if start > prev_end:
                    free.append((prev_end, start))
                prev_end = max(prev_end, end)
            if prev_end < work_end:
                free.append((prev_end, work_end))
            return free
        
        nicole_free = busy_to_free(nicole_busy, day)
        ruth_free = busy_to_free(ruth_busy, day)
        
        # Apply Ruth's Wednesday after 13:30 constraint
        if day == "Wednesday":
            # Trim ruth_free slots to end by 13:30
            new_ruth_free = []
            for s, e in ruth_free:
                if e > ruth_wed_cutoff:
                    e = ruth_wed_cutoff
                if s < e:
                    new_ruth_free.append((s, e))
            ruth_free = new_ruth_free
        
        # Find overlapping free slots of at least duration
        for ns, ne in nicole_free:
            for rs, re in ruth_free:
                overlap_start = max(ns, rs)
                overlap_end = min(ne, re)
                if overlap_end - overlap_start >= duration:
                    # Found a slot
                    print(f"{day}:{minutes_to_time(overlap_start)}-{minutes_to_time(overlap_start + duration)}")
                    return
    
    print("No suitable time found")

if __name__ == "__main__":
    schedule_meeting()