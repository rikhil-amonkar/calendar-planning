from datetime import datetime, timedelta

def parse_busy_times(busy_times_str):
    busy_times = []
    for day_times in busy_times_str.split(';'):
        day, times = day_times.strip().split(' during ')
        times = times.split(', ')
        for time in times:
            start, end = time.split(' to ')
            busy_times.append((day.strip(), start.strip(), end.strip()))
    return busy_times

def generate_slots(start_time, end_time, duration):
    current = start_time
    slots = []
    while current + duration <= end_time:
        slots.append((current, current + duration))
        current += timedelta(minutes=30)  # Check every 30 minutes for better precision
    return slots

def find_available_slots(busy_times, work_start, work_end, duration):
    available_slots = {}
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    for day in days_of_week:
        slots = generate_slots(work_start, work_end, duration)
        for busy_start, busy_end in busy_times.get(day, []):
            busy_start_dt = datetime.strptime(busy_start, "%H:%M")
            busy_end_dt = datetime.strptime(busy_end, "%H:%M")
            slots = [slot for slot in slots if not (busy_start_dt <= slot[1] and busy_end_dt >= slot[0])]
        available_slots[day] = slots
    
    return available_slots

def find_common_free_time(nicole_slots, daniel_slots):
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    for day in days_of_week:
        common_slots = set(nicole_slots[day]).intersection(daniel_slots[day])
        if common_slots:
            return day, min(common_slots)
    return None, None

# Work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(hours=1)

# Nicole and Daniel's busy times
nicole_busy_times_str = "Tuesday during 16:00 to 16:30, Wednesday during 15:00 to 15:30, Friday during 12:00 to 12:30, 15:30 to 16:00"
daniel_busy_times_str = "Monday during 9:00 to 12:30, 13:00 to 13:30, 14:00 to 16:30, Tuesday during 9:00 to 10:30, 11:30 to 12:30, 13:00 to 13:30, 15:00 to 16:00, 16:30 to 17:00, Wednesday during 9:00 to 10:00, 11:00 to 12:30, 13:00 to 13:30, 14:00 to 14:30, 16:30 to 17:00, Thursday during 11:00 to 12:00, 13:00 to 14:00, 15:00 to 15:30, Friday during 10:00 to 11:00, 11:30 to 12:00, 12:30 to 14:30, 15:00 to 15:30, 16:00 to 16:30"

# Parse busy times
nicole_busy_times = parse_busy_times(nicole_busy_times_str)
daniel_busy_times = parse_busy_times(daniel_busy_times_str)

# Convert busy times to a dictionary by day
nicole_busy_dict = {day: [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in times] for day, start, end in nicole_busy_times}
daniel_busy_dict = {day: [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in times] for day, start, end in daniel_busy_times}

# Find available slots
nicole_available_slots = find_available_slots(nicole_busy_dict, work_start, work_end, meeting_duration)
daniel_available_slots = find_available_slots(daniel_busy_dict, work_start, work_end, meeting_duration)

# Find common free time
day, slot = find_common_free_time(nicole_available_slots, daniel_available_slots)

# Output the result
if day and slot:
    start_time_str = slot[0].strftime("%H:%M")
    end_time_str = slot[1].strftime("%H:%M")
    print(f"{day} {start_time_str}:{end_time_str}")
else:
    print("No common free time found.")