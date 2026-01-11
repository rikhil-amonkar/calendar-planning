from datetime import datetime, timedelta

def parse_schedule(schedule_str):
    """Convert a schedule string to a list of datetime tuples."""
    busy_times = []
    for entry in schedule_str.split(','):
        start, end = entry.strip().split(' to ')
        busy_times.append((datetime.strptime(start, '%H:%M'), datetime.strptime(end, '%H:%M')))
    return busy_times

def is_time_slot_busy(slot_start, slot_end, busy_times):
    """Check if a time slot overlaps with any busy times."""
    for busy_start, busy_end in busy_times:
        if slot_start < busy_end and slot_end > busy_start:
            return True
    return False

def find_available_slot(participants, meeting_duration, preferred_days, start_time, end_time, constraints):
    """Find an available slot for the meeting."""
    meeting_duration = timedelta(minutes=meeting_duration)
    for day in preferred_days:
        day_start = datetime.strptime(f"{day} {start_time}", '%A %H:%M')
        day_end = datetime.strptime(f"{day} {end_time}", '%A %H:%M')
        current_time = day_start
        
        # Get busy times for each participant on the current day
        busy_times = []
        for participant, schedule in participants.items():
            busy_times.extend([(time[0].replace(day=day_start.day), time[1].replace(day=day_start.day)) for time in schedule if time[0].weekday() == day_start.weekday()])
        
        # Apply constraints
        if day == 'Monday':
            constraint_time = datetime.strptime("Monday 16:00", '%A %H:%M')
            day_end = min(day_end, constraint_time)
        
        # Find available slot
        while current_time + meeting_duration <= day_end:
            if not is_time_slot_busy(current_time, current_time + meeting_duration, busy_times):
                return current_time.strftime('%H:%M'), (current_time + meeting_duration).strftime('%H:%M'), day
            current_time += timedelta(minutes=15)  # Check every 15 minutes for better granularity
    
    return None

# Define the schedules
schedules = {
    "Tyler": parse_schedule("Tuesday 9:00 to 9:30, Tuesday 14:30 to 15:00, Wednesday 10:30 to 11:00, Wednesday 12:30 to 13:00, Wednesday 13:30 to 14:00, Wednesday 16:30 to 17:00"),
    "Ruth": parse_schedule("Monday 9:00 to 10:00, Monday 10:30 to 12:00, Monday 12:30 to 14:30, Monday 15:00 to 16:00, Monday 16:30 to 17:00, Tuesday 9:00 to 17:00, Wednesday 9:00 to 17:00")
}

# Define the meeting parameters
meeting_duration = 30
preferred_days = ["Monday", "Tuesday", "Wednesday"]
start_time = "9:00"
end_time = "17:00"
constraints = {"Tyler": {"Monday": "16:00"}}

# Find the available slot
available_slot = find_available_slot(schedules, meeting_duration, preferred_days, start_time, end_time, constraints)

if available_slot:
    print(f"Meeting time: {available_slot[0]}:{available_slot[1]} on {available_slot[2]}")
else:
    print("No available slot found.")