from datetime import datetime, timedelta

# Define the meeting day and working hours (Monday 09:00 - 17:00)
day = "Monday"
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define each person's busy intervals as tuples (start, end) in datetime objects.
# Convert time strings into datetime objects for the day (we only care about the time)
def to_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

busy_times = {
    "Shirley": [(to_time("10:30"), to_time("11:00")),
                (to_time("12:00"), to_time("12:30"))],
    "Jacob":   [(to_time("09:00"), to_time("09:30")),
                (to_time("10:00"), to_time("10:30")),
                (to_time("11:00"), to_time("11:30")),
                (to_time("12:30"), to_time("13:30")),
                (to_time("14:30"), to_time("15:00"))],
    "Stephen": [(to_time("11:30"), to_time("12:00")),
                (to_time("12:30"), to_time("13:00"))],
    "Margaret": [(to_time("09:00"), to_time("09:30")),
                 (to_time("10:30"), to_time("12:30")),
                 (to_time("13:00"), to_time("13:30")),
                 (to_time("15:00"), to_time("15:30")),
                 (to_time("16:30"), to_time("17:00"))],
    "Mason":   [(to_time("09:00"), to_time("10:00")),
                (to_time("10:30"), to_time("11:00")),
                (to_time("11:30"), to_time("12:30")),
                (to_time("13:00"), to_time("13:30")),
                (to_time("14:00"), to_time("14:30")),
                (to_time("16:30"), to_time("17:00"))]
}

# Additional constraint for Margaret: cannot meet before 14:30 on Monday.
margaret_earliest = to_time("14:30")

# Function to check if a given time slot is free for a person.
def is_slot_free(person, start, end):
    for busy_start, busy_end in busy_times[person]:
        # If the meeting overlaps with a busy period, then return False.
        # Overlap exists if start < busy_end and busy_start < end.
        if start < busy_end and busy_start < end:
            return False
    return True

# Function to check if a proposed meeting slot is free for all participants.
def is_slot_free_for_all(start, end):
    for person in busy_times:
        # For Margaret, also check the constraint that meeting start must be at or after 14:30.
        if person == "Margaret" and start < margaret_earliest:
            return False
        if not is_slot_free(person, start, end):
            return False
    return True

# Search for a candidate time slot
current_start = work_start
# We only search times that are within working hours and also satisfy Margaret's preference.
if current_start < margaret_earliest:
    current_start = margaret_earliest

found_slot = None
while current_start + meeting_duration <= work_end:
    current_end = current_start + meeting_duration
    if is_slot_free_for_all(current_start, current_end):
        found_slot = (current_start, current_end)
        break
    # Increment by 15 minutes for candidate slots.
    current_start += timedelta(minutes=15)

# Output the result in the format "HH:MM:HH:MM" and the day of the week.
if found_slot:
    start_str = found_slot[0].strftime("%H:%M")
    end_str = found_slot[1].strftime("%H:%M")
    print(f"{day} {start_str}:{end_str}")
else:
    print("No available meeting slot found.")