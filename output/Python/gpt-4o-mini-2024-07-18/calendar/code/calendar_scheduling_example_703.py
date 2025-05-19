from datetime import datetime, timedelta

# Define the working hours and the durations
working_hours = {
    "Monday": (9, 17),
    "Tuesday": (9, 17),
    "Wednesday": (9, 17)
}
meeting_duration = timedelta(hours=1)

# Existing schedules
schedules = {
    "Stephanie": {
        "Monday": [(9, 30), (10, 30), (11, 30), (14, 0)],  # end times derived
        "Tuesday": [(12, 0)],
        "Wednesday": [(9, 0), (13, 0)]  
    },
    "Betty": {
        "Monday": [(9, 0), (11, 0), (14, 30), (15, 30)],
        "Tuesday": [(9, 0), (11, 30), (12, 30), (15, 30)],
        "Wednesday": [(10, 0), (12, 0), (14, 30)]
    }
}

# Block out times on their schedules
def get_unavailable_times(schedule):
    unavailable_times = []
    for day, times in schedule.items():
        for time in times:
            start_time = datetime.strptime(f"{day} {time[0]}:{time[1]}", "%A %H:%M")
            end_time = start_time + timedelta(minutes=30)
            unavailable_times.append((start_time, end_time))
    return unavailable_times

# Calculate the available time slots for a given day
def find_available_slots(day):
    start_hour, end_hour = working_hours[day]
    day_start = datetime.strptime(f"{day} {start_hour}:00", "%A %H:%M")
    day_end = datetime.strptime(f"{day} {end_hour}:00", "%A %H:%M")
    
    # Get unavailable times for both participants
    unavailable_times = []
    unavailable_times += get_unavailable_times(schedules["Stephanie"].get(day, []))
    unavailable_times += get_unavailable_times(schedules["Betty"].get(day, []))
    
    # Sort by start time
    unavailable_times.sort()

    # Find available slots
    available_slots = []
    current_time = day_start

    for start, end in unavailable_times:
        # Check if there's a gap before the next meeting
        if current_time < start:
            while current_time + meeting_duration <= start:
                available_slots.append((current_time, current_time + meeting_duration))
                current_time += timedelta(minutes=30)  # Increment by 30 minutes

        # Move current time to the end of the unavailable block
        current_time = max(current_time, end)

    # Check for any remaining time after the last unavailable block
    if current_time + meeting_duration <= day_end:
        available_slots.append((current_time, current_time + meeting_duration))

    return available_slots

# Main logic to find meeting time
def schedule_meeting():
    for day in working_hours.keys():
        available_slots = find_available_slots(day)
        if available_slots:
            meeting_time = available_slots[0]  # Take the first available slot
            return f"{meeting_time[0].strftime('%H:%M')}:{meeting_time[1].strftime('%H:%M')} {day}"
    
    return "No available times found"

# Execute the scheduling function
scheduled_time = schedule_meeting()
print(scheduled_time)