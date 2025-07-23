def find_meeting_time(participants_schedules, work_hours, duration, constraints):
    # Parse work hours
    work_start, work_end = work_hours.split(" to ")
    work_start = int(work_start.split(':')[0]) + int(work_start.split(':')[1]) / 60
    work_end = int(work_end.split(':')[0]) + int(work_end.split(':')[1]) / 60

    # Initialize available slots for each participant
    available_slots = {}
    for participant, schedules in participants_schedules.items():
        # Start with the full work day as available
        available = [(work_start, work_end)]
        
        # Subtract blocked times
        for block in schedules:
            block_start, block_end = block.split(" to ")
            block_start = int(block_start.split(':')[0]) + int(block_start.split(':')[1]) / 60
            block_end = int(block_end.split(':')[0]) + int(block_end.split(':')[1]) / 60
            
            new_available = []
            for slot in available:
                if block_end <= slot[0] or block_start >= slot[1]:
                    # No overlap
                    new_available.append(slot)
                else:
                    # Split the available slot around the block
                    if slot[0] < block_start:
                        new_available.append((slot[0], block_start))
                    if block_end < slot[1]:
                        new_available.append((block_end, slot[1]))
            available = new_available
        
        available_slots[participant] = available

    # Apply constraints
    for participant, constraint in constraints.items():
        if constraint == "can not meet after 15:00":
            new_available = []
            for slot in available_slots[participant]:
                if slot[1] <= 15.0:
                    new_available.append(slot)
                elif slot[0] < 15.0:
                    new_available.append((slot[0], 15.0))
            available_slots[participant] = new_available

    # Find overlapping available slots
    common_slots = []
    for slot1 in available_slots["Christine"]:
        for slot2 in available_slots["Helen"]:
            start = max(slot1[0], slot2[0])
            end = min(slot1[1], slot2[1])
            if end - start >= duration / 60:
                common_slots.append((start, end))

    if not common_slots:
        return None

    # Select the first available slot
    meeting_start, meeting_end = common_slots[0]
    meeting_end = meeting_start + duration / 60

    # Format the output
    def float_to_time(time_float):
        hours = int(time_float)
        minutes = int((time_float - hours) * 60)
        return f"{hours:02d}:{minutes:02d}"

    return f"{float_to_time(meeting_start)}:{float_to_time(meeting_end)}"

# Define inputs
participants_schedules = {
    "Christine": ["11:00 to 11:30", "15:00 to 15:30"],
    "Helen": ["9:30 to 10:30", "11:00 to 11:30", "12:00 to 12:30", "13:30 to 16:00", "16:30 to 17:00"]
}

work_hours = "9:00 to 17:00"
duration = 30  # minutes
constraints = {"Helen": "can not meet after 15:00"}

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours, duration, constraints)

# Output the result
print(f"Monday:{meeting_time}")