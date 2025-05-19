from datetime import time, timedelta

def parse_busy_slots(busy_times):
    slots = []
    for day_schedule in busy_times:
        day, intervals = day_schedule.split(" during ")[0], day_schedule.split(" during ")[1].split(", ")
        for interval in intervals:
            start_str, end_str = interval.split(" to ")
            start = time.fromisoformat(start_str.replace(':', ''))
            end = time.fromisoformat(end_str.replace(':', ''))
            slots.append((day, start, end))
    return slots

carl_busy = [
    "Monday during 11:00 to 11:30",
    "Tuesday during 14:30 to 15:00",
    "Wednesday during 10:00 to 11:30, 13:00 to 13:30",
    "Thursday during 13:30 to 14:00, 16:00 to 16:30"
]

margaret_busy = [
    "Monday during 9:00 to 10:30, 11:00 to 17:00",
    "Tuesday during 9:30 to 12:00, 13:30 to 14:00, 15:30 to 17:00",
    "Wednesday during 9:30 to 12:00, 12:30 to 13:00, 13:30 to 14:30, 15:00 to 17:00",
    "Thursday during 10:00 to 12:00, 12:30 to 14:00, 14:30 to 17:00"
]

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_start = time(9, 0)
work_end = time(17, 0)
duration = timedelta(hours=1)

carl_slots = parse_busy_slots(carl_busy)
margaret_slots = parse_busy_slots(margaret_busy)

def find_slot(day):
    current_start = work_start
    while True:
        current_end = (datetime.combine(datetime.today(), current_start) + duration).time()
        if current_end > work_end:
            break
        
        # Check Carl's availability
        carl_conflict = any(
            d == day and not (current_end <= start or current_start >= end)
            for (d, start, end) in carl_slots
        )
        
        # Check Margaret's availability
        margaret_conflict = any(
            d == day and not (current_end <= start or current_start >= end)
            for (d, start, end) in margaret_slots
        )
        
        if not carl_conflict and not margaret_conflict:
            return (current_start, current_end)
        
        current_start = (datetime.combine(datetime.today(), current_start) + timedelta(minutes=15)).time()
    
    return None

# Check days in preferred order (excluding Thursday if possible)
for day in ["Tuesday", "Monday", "Wednesday", "Thursday"]:
    slot = find_slot(day)
    if slot and (day != "Thursday" or slot[0] >= time(14, 30)):
        start_time = slot[0].strftime("%H:%M")
        end_time = slot[1].strftime("%H:%M")
        print(f"{day}:{start_time}:{end_time}")
        break