from datetime import datetime, timedelta

def find_meeting_time(participants_availability, meeting_duration, work_hours):
    start_of_day = datetime.strptime(work_hours[0], "%H:%M")
    end_of_day = datetime.strptime(work_hours[1], "%H:%M")

    # Convert participants' busy times to datetime format
    busy_slots = []
    for availability in participants_availability:
        for busy_time in availability:
            busy_start = datetime.strptime(busy_time[0], "%H:%M")
            busy_end = datetime.strptime(busy_time[1], "%H:%M")
            busy_slots.append((busy_start, busy_end))

    # Sort the busy slots
    busy_slots.sort()

    # Check for available time
    last_end = start_of_day
    for busy_start, busy_end in busy_slots:
        # Check for a gap before the busy time
        if last_end + timedelta(minutes=meeting_duration) <= busy_start:
            return f"{last_end.strftime('%H:%M')}:{(last_end + timedelta(minutes=meeting_duration)).strftime('%H:%M')}"

        # Update last_end to the end of the busy slot if it's more recent
        last_end = max(last_end, busy_end)

    # After the last busy slot, check if there's time until end of day
    if last_end + timedelta(minutes=meeting_duration) <= end_of_day:
        return f"{last_end.strftime('%H:%M')}:{(last_end + timedelta(minutes=meeting_duration)).strftime('%H:%M')}"

    return None

# Participants' availability
participants_availability = [
    [("09:30", "10:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("16:30", "17:00")],  # Adam
    [("10:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("16:30", "17:00")]   # Roy
]

# Meeting duration in minutes
meeting_duration = 30

# Work hours
work_hours = ["09:00", "17:00"]

# Find the meeting time
meeting_time = find_meeting_time(participants_availability, meeting_duration, work_hours)

if meeting_time:
    day_of_week = "Monday"
    print(f"{meeting_time}:{day_of_week}")