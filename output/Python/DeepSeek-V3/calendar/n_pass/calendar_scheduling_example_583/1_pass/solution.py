def find_meeting_time(lisa_busy, anthony_busy, work_hours, duration_minutes):
    # Convert busy times to minutes since start of day
    def parse_time(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def to_time_str(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    start_work, end_work = map(parse_time, work_hours.split(' to '))
    duration = duration_minutes
    
    # Generate free slots for Lisa
    lisa_free = []
    prev_end = start_work
    for busy in lisa_busy:
        busy_start, busy_end = map(parse_time, busy.split(' to '))
        if busy_start > prev_end:
            lisa_free.append((prev_end, busy_start))
        prev_end = busy_end
    if prev_end < end_work:
        lisa_free.append((prev_end, end_work))
    
    # Generate free slots for Anthony
    anthony_free = []
    prev_end = start_work
    for busy in anthony_busy:
        busy_start, busy_end = map(parse_time, busy.split(' to '))
        if busy_start > prev_end:
            anthony_free.append((prev_end, busy_start))
        prev_end = busy_end
    if prev_end < end_work:
        anthony_free.append((prev_end, end_work))
    
    # Find overlapping free slots
    for lisa_start, lisa_end in lisa_free:
        for anthony_start, anthony_end in anthony_free:
            start = max(lisa_start, anthony_start)
            end = min(lisa_end, anthony_end)
            if end - start >= duration:
                return (start, start + duration)
    
    return None

# Input data
day = "Monday"
work_hours = "9:00 to 17:00"
duration_minutes = 30
lisa_busy = ["9:00 to 9:30", "10:30 to 11:00", "14:00 to 16:00"]
anthony_busy = [
    "9:00 to 9:30", "11:00 to 11:30", "12:30 to 13:30",
    "14:00 to 15:00", "15:30 to 16:00", "16:30 to 17:00"
]

# Find meeting time
meeting_time = find_meeting_time(lisa_busy, anthony_busy, work_hours, duration_minutes)

if meeting_time:
    start, end = meeting_time
    start_str = f"{start // 60:02d}:{start % 60:02d}"
    end_str = f"{end // 60:02d}:{end % 60:02d}"
    print(f"{day}: {start_str}:{end_str}")
else:
    print("No suitable meeting time found.")