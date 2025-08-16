from datetime import datetime, timedelta

def find_meeting_time(participants, day, meeting_duration, max_time):
    # Convert times to datetime objects for easier manipulation
    start_of_day = datetime.strptime(f"{day} 09:00", "%A %H:%M")
    end_of_day = datetime.strptime(f"{day} 17:00", "%A %H:%M")
    max_time = datetime.strptime(f"{day} {max_time}", "%A %H:%M")

    # Initialize available time slots
    available_slots = [(start_of_day, end_of_day)]

    # Remove booked times from the available slots
    for person, booked_times in participants.items():
        for start, end in booked_times:
            start = datetime.strptime(f"{day} {start.split()[1]}", "%A %H:%M")
            end = datetime.strptime(f"{day} {end.split()[1]}", "%A %H:%M")
            new_slots = []
            for slot_start, slot_end in available_slots:
                if start <= slot_end and end >= slot_start:  # Overlapping times
                    if start > slot_start:
                        new_slots.append((slot_start, start))
                    if end < slot_end:
                        new_slots.append((end, slot_end))
                else:
                    new_slots.append((slot_start, slot_end))
            available_slots = new_slots

    # Find a slot that fits the meeting duration and is before max_time
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= timedelta(hours=meeting_duration) and slot_end <= max_time:
            meeting_start = slot_start.time().strftime("%H:%M")
            meeting_end = (slot_start + timedelta(hours=meeting_duration)).time().strftime("%H:%M")
            return f"{meeting_start}-{meeting_end}", day

    return None, None

# Define participants' schedules
participants = {
    "Ryan": [("Monday 09:00", "Monday 09:30"), ("Monday 12:30", "Monday 13:00")],
    "Ruth": [],
    "Denise": [("Monday 09:30", "Monday 10:30"), ("Monday 12:00", "Monday 13:00"), ("Monday 14:30", "Monday 16:30")]
}

# Meeting details
day = "Monday"
meeting_duration = 1  # in hours
max_time = "12:30"

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time(participants, day, meeting_duration, max_time)
if meeting_time:
    print(f"Meeting time: {meeting_time} on {meeting_day}")
else:
    print("No available meeting time found.")