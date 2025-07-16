from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def parse_busy_slots(busy_slots):
    parsed_slots = []
    for slot in busy_slots:
        start, end = slot.split(" to ")
        parsed_slots.append((parse_time(start), parse_time(end)))
    return parsed_slots

def is_available(day, start_time, end_time, person_busy_slots):
    for busy_start, busy_end in person_busy_slots.get(day, []):
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    return True

def find_meeting_time(daniel_busy, bradley_busy, duration, work_hours_start, work_hours_end, days):
    duration = timedelta(minutes=duration)
    work_start = parse_time(work_hours_start)
    work_end = parse_time(work_hours_end)
    
    for day in days:
        current_time = datetime.combine(datetime.today(), work_start)
        end_of_day = datetime.combine(datetime.today(), work_end)
        
        while current_time + duration <= end_of_day:
            slot_start = current_time.time()
            slot_end = (current_time + duration).time()
            
            # Check Daniel's preferences
            if day == "Wednesday" or day == "Thursday":
                current_time += timedelta(minutes=15)
                continue
            
            # Check Bradley's preferences
            if day == "Monday":
                current_time += timedelta(minutes=15)
                continue
            if day == "Tuesday" and slot_start < parse_time("12:00"):
                current_time += timedelta(minutes=15)
                continue
            if day == "Friday":
                current_time += timedelta(minutes=15)
                continue
            
            # Check availability
            daniel_available = is_available(day, slot_start, slot_end, daniel_busy)
            bradley_available = is_available(day, slot_start, slot_end, bradley_busy)
            
            if daniel_available and bradley_available:
                return day, slot_start, slot_end
            
            current_time += timedelta(minutes=15)
    
    return None, None, None

# Define busy slots for Daniel and Bradley
daniel_busy = {
    "Monday": parse_busy_slots(["9:30 to 10:30", "12:00 to 12:30", "13:00 to 14:00", "14:30 to 15:00", "15:30 to 16:00"]),
    "Tuesday": parse_busy_slots(["11:00 to 12:00", "13:00 to 13:30", "15:30 to 16:00", "16:30 to 17:00"]),
    "Wednesday": parse_busy_slots(["9:00 to 10:00", "14:00 to 14:30"]),
    "Thursday": parse_busy_slots(["10:30 to 11:00", "12:00 to 13:00", "14:30 to 15:00", "15:30 to 16:00"]),
    "Friday": parse_busy_slots(["9:00 to 9:30", "11:30 to 12:00", "13:00 to 13:30", "16:30 to 17:00"]),
}

bradley_busy = {
    "Monday": parse_busy_slots(["9:30 to 11:00", "11:30 to 12:00", "12:30 to 13:00", "14:00 to 15:00"]),
    "Tuesday": parse_busy_slots(["10:30 to 11:00", "12:00 to 13:00", "13:30 to 14:00", "15:30 to 16:30"]),
    "Wednesday": parse_busy_slots(["9:00 to 10:00", "11:00 to 13:00", "13:30 to 14:00", "14:30 to 17:00"]),
    "Thursday": parse_busy_slots(["9:00 to 12:30", "13:30 to 14:00", "14:30 to 15:00", "15:30 to 16:30"]),
    "Friday": parse_busy_slots(["9:00 to 9:30", "10:00 to 12:30", "13:00 to 13:30", "14:00 to 14:30", "15:30 to 16:30"]),
}

# Define meeting parameters
meeting_duration = 30
work_hours_start = "9:00"
work_hours_end = "17:00"
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Find meeting time
day, start_time, end_time = find_meeting_time(
    daniel_busy, bradley_busy, meeting_duration, work_hours_start, work_hours_end, days
)

# Output the result with corrected formatting
if day and start_time and end_time:
    print(f"{day}: {start_time.strftime('%H:%M')} to {end_time.strftime('%H:%M')}")
else:
    print("No suitable meeting time found.")