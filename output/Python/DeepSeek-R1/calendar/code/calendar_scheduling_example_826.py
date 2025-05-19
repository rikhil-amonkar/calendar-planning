import datetime

def parse_time(time_str):
    return datetime.datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time):
    return time.hour * 60 + time.minute

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_meeting_slot():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    james_busy = {
        "Monday": ["9:00-9:30", "10:30-11:00", "12:30-13:00", "14:30-15:30", "16:30-17:00"],
        "Tuesday": ["9:00-11:00", "11:30-12:00", "12:30-15:30", "16:00-17:00"],
        "Wednesday": ["10:00-11:00", "12:00-13:00", "13:30-16:00"],
        "Thursday": ["9:30-11:30", "12:00-12:30", "13:00-13:30", "14:00-14:30", "16:30-17:00"]
    }
    
    preferred_days = ["Monday", "Tuesday"]  # Cheryl's preference excludes Wed/Thu
    
    for day in preferred_days:
        busy_intervals = []
        for slot in james_busy[day]:
            start_str, end_str = slot.split("-")
            start = time_to_minutes(parse_time(start_str))
            end = time_to_minutes(parse_time(end_str))
            busy_intervals.append((start, end))
        
        busy_intervals.sort()
        free_slots = []
        prev_end = work_start
        
        for start, end in busy_intervals:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                start_time = minutes_to_time_str(meeting_start)
                end_time = minutes_to_time_str(meeting_end)
                return f"{day} {start_time}-{end_time}"
    
    return "No available slot"

result = find_meeting_slot()
day, time_range = result.split()
start, end = time_range.split("-")
print(f"{day} {start}:{end}")