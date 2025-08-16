from datetime import datetime, timedelta

def find_meeting_time(stephanie_schedule, betty_schedule, preferred_days, meeting_duration, stephanie_avoid_day, betty_tuesday_limit):
    # Convert times to datetime objects for easier manipulation
    def parse_time(time_str):
        return datetime.strptime(time_str, "%H:%M")
    
    # Generate available slots for each participant
    def generate_slots(schedule, start_time="09:00", end_time="17:00"):
        start = parse_time(start_time)
        end = parse_time(end_time)
        slots = []
        current = start
        while current < end:
            next_slot = current + timedelta(hours=meeting_duration)
            if next_slot <= end and all(not (current >= busy_start and current < busy_end) and not (next_slot > busy_start and next_slot <= busy_end) for busy_start, busy_end in schedule):
                slots.append((current, next_slot))
            current += timedelta(minutes=30)  # Check every 30 minutes for finer granularity
        return slots
    
    # Main logic to find a common slot
    for day in preferred_days:
        stephanie_slots = generate_slots(stephanie_schedule.get(day, []))
        betty_slots = generate_slots(betty_schedule.get(day, []))
        
        if day == stephanie_avoid_day:
            continue
        
        if day == "Tuesday":
            betty_slots = [slot for slot in betty_slots if slot[1] <= parse_time(betty_tuesday_limit)]
        
        for stephanie_slot in stephanie_slots:
            for betty_slot in betty_slots:
                if stephanie_slot[0] >= betty_slot[0] and stephanie_slot[1] <= betty_slot[1]:
                    return f"{stephanie_slot[0].strftime('%H:%M')}:{stephanie_slot[1].strftime('%H:%M')}", day
    
    return None, None

# Input data
stephanie_schedule = {
    "Monday": [(parse_time("09:30"), parse_time("10:00")), (parse_time("10:30"), parse_time("11:00")), (parse_time("11:30"), parse_time("12:00")), (parse_time("14:00"), parse_time("14:30"))],
    "Tuesday": [(parse_time("12:00"), parse_time("13:00"))],
    "Wednesday": [(parse_time("09:00"), parse_time("10:00")), (parse_time("13:00"), parse_time("14:00"))]
}

betty_schedule = {
    "Monday": [(parse_time("09:00"), parse_time("10:00")), (parse_time("11:00"), parse_time("11:30")), (parse_time("14:30"), parse_time("15:00")), (parse_time("15:30"), parse_time("16:00"))],
    "Tuesday": [(parse_time("09:00"), parse_time("09:30")), (parse_time("11:30"), parse_time("12:00")), (parse_time("12:30"), parse_time("14:30")), (parse_time("15:30"), parse_time("16:00"))],
    "Wednesday": [(parse_time("10:00"), parse_time("11:30")), (parse_time("12:00"), parse_time("14:00")), (parse_time("14:30"), parse_time("17:00"))]
}

preferred_days = ["Monday", "Tuesday", "Wednesday"]
meeting_duration = 1  # in hours
stephanie_avoid_day = "Monday"
betty_tuesday_limit = "12:30"

# Find the meeting time
time_range, day_of_week = find_meeting_time(stephanie_schedule, betty_schedule, preferred_days, meeting_duration, stephanie_avoid_day, betty_tuesday_limit)

# Output the result
print(f"{time_range}, {day_of_week}")