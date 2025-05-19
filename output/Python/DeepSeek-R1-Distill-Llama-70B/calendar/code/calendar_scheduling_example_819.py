# Define the work hours and meeting duration
work_start = "09:00"
work_end = "17:00"
meeting_duration = 30  # in minutes

# Define participants' schedules and preferences
participants = {
    "Julie": {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [],
        "Thursday": []
    },
    "Ruth": {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:00", "17:00")],
        "Wednesday": [("09:00", "17:00")],
        "Thursday": [("09:00", "11:00"), ("11:30", "14:30"), ("15:00", "17:00")]
    }
}

# Julie's preference to avoid meetings on Thursday before 11:30
julie_preference = {
    "Thursday": "11:30"
}

# Convert time strings to minutes since midnight for easier calculations
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Convert minutes back to HH:MM format
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Find the earliest available time slot that fits all constraints
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_start_minutes = time_to_minutes(work_start)
work_end_minutes = time_to_minutes(work_end)
meeting_end_minutes = work_start_minutes + meeting_duration

# Iterate through each day to find a suitable time
for day in days:
    # Initialize available time as the entire work day
    available_start = work_start_minutes
    available_end = work_end_minutes
    
    # Apply Julie's preference if it's Thursday
    if day == "Thursday":
        preference_time = julie_preference.get(day, "11:30")
        preference_minutes = time_to_minutes(preference_time)
        available_start = max(available_start, preference_minutes)
    
    # Check Julie's schedule for the day (Julie has no meetings)
    # Check Ruth's schedule for the day
    if day in participants["Ruth"]:
        for slot in participants["Ruth"][day]:
            slot_start = time_to_minutes(slot[0])
            slot_end = time_to_minutes(slot[1])
            
            if slot_end < available_start:
                continue  # Slot is before the preferred time
            elif slot_start > available_end:
                break  # No more relevant slots
            
            # Adjust available time around this slot
            if slot_start > available_start:
                available_start = slot_end
    
    # Ensure the meeting time is within work hours
    if available_start + meeting_duration > work_end_minutes:
        continue  # No available time slot on this day
    else:
        meeting_start = available_start
        meeting_end = meeting_start + meeting_duration
        print(f"Proposed meeting time: {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} on {day}")
        break