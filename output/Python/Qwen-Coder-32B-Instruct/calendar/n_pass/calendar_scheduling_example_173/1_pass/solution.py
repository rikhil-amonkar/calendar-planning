from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time, constraints):
    # Convert times to datetime objects for easier manipulation
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)

    # Create a list of available slots for each participant
    available_slots = {}
    for participant, blocks in participants.items():
        current_time = start_time
        slots = []
        while current_time + meeting_duration <= end_time:
            slot_end = current_time + meeting_duration
            if all(slot_end <= block_start or current_time >= block_end for block_start, block_end in blocks):
                slots.append((current_time, slot_end))
            current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
        available_slots[participant] = slots

    # Find common slots among all participants
    common_slots = set.intersection(*[set(slots) for slots in available_slots.values()])

    # Apply additional constraints
    valid_slots = [slot for slot in common_slots if slot[1] <= constraints.get('latest_time', end_time)]

    # Return the first valid slot found
    if valid_slots:
        return valid_slots[0]
    else:
        return None

# Define participants' schedules and constraints
participants = {
    'Jacqueline': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                   (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                   (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                   (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    'Harold': [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Arthur': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Kelly': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
              (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]
}

constraints = {
    'latest_time': datetime.strptime("13:00", "%H:%M")  # Harold's constraint
}

# Find a suitable meeting time
meeting_time = find_meeting_time(participants, 30, "09:00", "17:00", constraints)

# Output the result
if meeting_time:
    print(f"{meeting_time[0].strftime('%H:%M')}:{meeting_time[1].strftime('%H:%M')} Monday")
else:
    print("No suitable meeting time found.")