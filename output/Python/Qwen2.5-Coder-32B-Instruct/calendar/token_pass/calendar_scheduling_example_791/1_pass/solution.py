from datetime import datetime, timedelta

def parse_schedule(schedule_str):
    """Parses a string of busy times and returns a list of tuples (start, end)"""
    busy_times = []
    for entry in schedule_str.split(', '):
        start, end = entry.split(' to ')
        busy_times.append((datetime.strptime(start, '%H:%M'), datetime.strptime(end, '%H:%M')))
    return busy_times

def find_free_slots(busy_times, work_start, work_end):
    """Finds free slots in a day given busy times and work hours"""
    current_time = work_start
    free_slots = []
    
    for start, end in sorted(busy_times):
        if current_time < start:
            free_slots.append((current_time, start))
        current_time = max(current_time, end)
    
    if current_time < work_end:
        free_slots.append((current_time, work_end))
    
    return free_slots

def find_common_free_slot(nicole_busy, ruth_busy, work_start, work_end, meeting_duration):
    """Finds a common free slot between Nicole and Ruth's schedules"""
    nicole_free = find_free_slots(nicole_busy, work_start, work_end)
    ruth_free = find_free_slots(ruth_busy, work_start, work_end)
    
    for n_start, n_end in nicole_free:
        for r_start, r_end in ruth_free:
            common_start = max(n_start, r_start)
            common_end = min(n_end, r_end)
            if (common_end - common_start) >= meeting_duration:
                return common_start, common_end
    return None

def main():
    # Define work hours
    work_start = datetime.strptime('09:00', '%H:%M')
    work_end = datetime.strptime('17:00', '%H:%M')
    meeting_duration = timedelta(minutes=30)
    
    # Parse schedules
    nicole_schedule = "9:00 to 9:30, 13:00 to 13:30, 14:30 to 15:30"
    ruth_schedule = "9:00 to 17:00, 9:00 to 17:00, 9:00 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:30 to 15:30, 16:00 to 16:30"
    
    nicole_busy = parse_schedule(nicole_schedule)
    ruth_busy = parse_schedule(ruth_schedule)
    
    # Check each day
    days = ["Monday", "Tuesday", "Wednesday"]
    for day in days:
        if day == "Monday":
            nicole_busy_day = nicole_busy[:3]
            ruth_busy_day = ruth_busy[:2]
        elif day == "Tuesday":
            nicole_busy_day = nicole_busy[3:6]
            ruth_busy_day = ruth_busy[:2]
        else:  # Wednesday
            nicole_busy_day = nicole_busy[6:]
            ruth_busy_day = ruth_busy[2:]
            work_end_wednesday = datetime.strptime('13:30', '%H:%M')  # Ruth's preference
        
        common_slot = find_common_free_slot(nicole_busy_day, ruth_busy_day, work_start, work_end_wednesday if day == "Wednesday" else work_end, meeting_duration)
        if common_slot:
            start_time, end_time = common_slot
            print(f"{day}, {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
            return

if __name__ == "__main__":
    main()