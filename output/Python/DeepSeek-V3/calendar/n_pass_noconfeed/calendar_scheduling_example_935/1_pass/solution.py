from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time):
    return time.hour * 60 + time.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return datetime.strptime(f"{hours:02d}:{minutes:02d}", "%H:%M").time()

def is_available(day, start_time, end_time, busy_slots):
    start_min = time_to_minutes(start_time)
    end_min = time_to_minutes(end_time)
    for slot in busy_slots.get(day, []):
        slot_start = time_to_minutes(slot[0])
        slot_end = time_to_minutes(slot[1])
        if not (end_min <= slot_start or start_min >= slot_end):
            return False
    return True

def find_earliest_meeting_slot(terry_busy, frances_busy, duration, days, work_start, work_end, avoid_day=None):
    duration_min = duration
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    for day in days:
        if avoid_day and day == avoid_day:
            continue
        current_time_min = work_start_min
        while current_time_min + duration_min <= work_end_min:
            start_time = minutes_to_time(current_time_min)
            end_time = minutes_to_time(current_time_min + duration_min)
            if (is_available(day, start_time, end_time, terry_busy) and 
                is_available(day, start_time, end_time, frances_busy)):
                return day, start_time, end_time
            current_time_min += 15  # Check in 15-minute increments
    return None, None, None

# Define work hours and meeting duration
work_start = parse_time("09:00")
work_end = parse_time("17:00")
meeting_duration = 30  # minutes
days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Define busy slots for Terry and Frances
terry_busy = {
    "Monday": [
        (parse_time("10:30"), parse_time("11:00")),
        (parse_time("12:30"), parse_time("14:00")),
        (parse_time("15:00"), parse_time("17:00"))
    ],
    "Tuesday": [
        (parse_time("09:30"), parse_time("10:00")),
        (parse_time("10:30"), parse_time("11:00")),
        (parse_time("14:00"), parse_time("14:30")),
        (parse_time("16:00"), parse_time("16:30"))
    ],
    "Wednesday": [
        (parse_time("09:30"), parse_time("10:30")),
        (parse_time("11:00"), parse_time("12:00")),
        (parse_time("13:00"), parse_time("13:30")),
        (parse_time("15:00"), parse_time("16:00")),
        (parse_time("16:30"), parse_time("17:00"))
    ],
    "Thursday": [
        (parse_time("09:30"), parse_time("10:00")),
        (parse_time("12:00"), parse_time("12:30")),
        (parse_time("13:00"), parse_time("14:30")),
        (parse_time("16:00"), parse_time("16:30"))
    ],
    "Friday": [
        (parse_time("09:00"), parse_time("11:30")),
        (parse_time("12:00"), parse_time("12:30")),
        (parse_time("13:30"), parse_time("16:00")),
        (parse_time("16:30"), parse_time("17:00"))
    ]
}

frances_busy = {
    "Monday": [
        (parse_time("09:30"), parse_time("11:00")),
        (parse_time("11:30"), parse_time("13:00")),
        (parse_time("14:00"), parse_time("14:30")),
        (parse_time("15:00"), parse_time("16:00"))
    ],
    "Tuesday": [
        (parse_time("09:00"), parse_time("09:30")),
        (parse_time("10:00"), parse_time("10:30")),
        (parse_time("11:00"), parse_time("12:00")),
        (parse_time("13:00"), parse_time("14:30")),
        (parse_time("15:30"), parse_time("16:30"))
    ],
    "Wednesday": [
        (parse_time("09:30"), parse_time("10:00")),
        (parse_time("10:30"), parse_time("11:00")),
        (parse_time("11:30"), parse_time("16:00")),
        (parse_time("16:30"), parse_time("17:00"))
    ],
    "Thursday": [
        (parse_time("11:00"), parse_time("12:30")),
        (parse_time("14:30"), parse_time("17:00"))
    ],
    "Friday": [
        (parse_time("09:30"), parse_time("10:30")),
        (parse_time("11:00"), parse_time("12:30")),
        (parse_time("13:00"), parse_time("16:00")),
        (parse_time("16:30"), parse_time("17:00"))
    ]
}

# Find the earliest meeting slot avoiding Tuesday if possible
day, start_time, end_time = find_earliest_meeting_slot(
    terry_busy, frances_busy, meeting_duration, days_of_week, work_start, work_end, "Tuesday"
)

if day is None:
    # If no slot found avoiding Tuesday, try including Tuesday
    day, start_time, end_time = find_earliest_meeting_slot(
        terry_busy, frances_busy, meeting_duration, days_of_week, work_start, work_end
    )

# Output the result
if day and start_time and end_time:
    print(f"{day}: {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
else:
    print("No suitable meeting time found.")