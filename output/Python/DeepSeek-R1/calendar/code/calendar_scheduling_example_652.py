from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_range(start, end):
    return (start.hour, start.minute), (end.hour, end.minute)

def is_available(busy_slots, start, end):
    for busy_start, busy_end in busy_slots:
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

jesse_busy = {
    "Monday": [("13:30", "14:00"), ("14:30", "15:00")],
    "Tuesday": [("09:00", "09:30"), ("13:00", "13:30"), ("14:00", "15:00")]
}

lawrence_busy = {
    "Monday": [("09:00", "17:00")],
    "Tuesday": [("09:30", "10:30"), ("11:30", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "16:30")]
}

days = ["Monday", "Tuesday"]
meeting_duration = timedelta(minutes=30)

for day in days:
    work_start = parse_time("09:00")
    work_end = parse_time("17:00") if day == "Monday" else parse_time("16:30")
    
    jesse_slots = [time_range(parse_time(s), parse_time(e)) for s, e in jesse_busy.get(day, [])]
    lawrence_slots = [time_range(parse_time(s), parse_time(e)) for s, e in lawrence_busy.get(day, [])]
    
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        slot_end = current_time + meeting_duration
        start = (current_time.hour, current_time.minute)
        end = (slot_end.hour, slot_end.minute)
        
        if (is_available(jesse_slots, start, end) and 
            is_available(lawrence_slots, start, end)):
            print(f"{day}")
            print(f"{current_time.strftime('%H:%M')}:{slot_end.strftime('%H:%M')}")
            exit()
        
        current_time += timedelta(minutes=15)

print("No suitable time found")