def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def is_slot_free(slot, busy_list):
    s, e = slot
    for (b_start, b_end) in busy_list:
        if e <= b_start or s >= b_end:
            continue
        else:
            return False
    return True

def main():
    # Work hours: 9:00 to 17:00
    work_start_min = 540   # 9:00 in minutes
    work_end_min = 1020    # 17:00 in minutes
    meeting_duration = 30   # 30 minutes
    last_start_min = work_end_min - meeting_duration   # 16:30 in minutes (990)

    # Days to check in order
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Busy intervals as strings (from input)
    ronald_busy_str = {
        'Monday': [('10:30','11:00'), ('12:00','12:30'), ('15:30','16:00')],
        'Tuesday': [('9:00','9:30'), ('12:00','12:30'), ('15:30','16:30')],
        'Wednesday': [('9:30','10:30'), ('11:00','12:00'), ('12:30','13:00'), ('13:30','14:00'), ('16:30','17:00')]
    }
    
    amber_busy_str = {
        'Monday': [('9:00','9:30'), ('10:00','10:30'), ('11:30','12:00'), ('12:30','14:00'), ('14:30','15:00'), ('15:30','17:00')],
        'Tuesday': [('9:00','9:30'), ('10:00','11:30'), ('12:00','12:30'), ('13:30','15:30'), ('16:30','17:00')],
        'Wednesday': [('9:00','9:30'), ('10:00','10:30'), ('11:00','13:30'), ('15:00','15:30')]
    }
    
    # Convert busy intervals to minutes
    ronald_busy_min = {}
    amber_busy_min = {}
    
    for day in days:
        ronald_busy_min[day] = []
        for (s, e) in ronald_busy_str[day]:
            s_min = time_str_to_minutes(s)
            e_min = time_str_to_minutes(e)
            ronald_busy_min[day].append((s_min, e_min))
            
        amber_busy_min[day] = []
        for (s, e) in amber_busy_str[day]:
            s_min = time_str_to_minutes(s)
            e_min = time_str_to_minutes(e)
            amber_busy_min[day].append((s_min, e_min))
    
    # Search for the earliest slot
    found = False
    for day in days:
        # Get busy lists for the day
        r_busy_today = ronald_busy_min[day]
        a_busy_today = amber_busy_min[day]
        
        # Check every possible 30-minute slot in the work day
        for start_min in range(work_start_min, last_start_min + 1, 30):
            slot = (start_min, start_min + meeting_duration)
            # Check if free for both Ronald and Amber
            if is_slot_free(slot, r_busy_today) and is_slot_free(slot, a_busy_today):
                start_str = minutes_to_time_str(start_min)
                end_str = minutes_to_time_str(start_min + meeting_duration)
                time_range_str = f"{start_str}:{end_str}"
                print(day)
                print(time_range_str)
                found = True
                return
    
    # According to the problem, there is a solution, so we should always find one.
    if not found:
        print("No suitable time found")

if __name__ == "__main__":
    main()