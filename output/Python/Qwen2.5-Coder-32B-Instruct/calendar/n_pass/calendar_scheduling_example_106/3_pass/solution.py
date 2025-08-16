from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end, day_of_week):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M").time()
    work_end = datetime.strptime(work_end, "%H:%M").time()
    meeting_duration = timedelta(hours=meeting_duration)
    
    def parse_time(time_str):
        return datetime.strptime(time_str, "%H:%M").time()
    
    # Function to merge free time slots for all participants
    def merge_free_slots(slots):
        if not slots:
            return []
        
        # Sort slots by start time
        slots.sort(key=lambda x: x[0])
        
        merged_slots = [slots[0]]
        for start, end in slots[1:]:
            last_start, last_end = merged_slots[-1]
            if start <= last_end:
                # Merge overlapping or adjacent slots
                merged_slots[-1] = (last_start, max(last_end, end))
            else:
                merged_slots.append((start, end))
        
        return merged_slots
    
    # Find available slots for each person
    all_available_slots = []
    for person, blocks in schedules.items():
        current_time = work_start
        available_slots = []
        for block in blocks:
            block_start, block_end = map(parse_time, block)
            if current_time < block_start:
                available_slots.append((current_time, block_start))
            current_time = max(current_time, block_end)
        if current_time < work_end:
            available_slots.append((current_time, work_end))
        all_available_slots.extend(available_slots)
    
    # Merge available slots for all participants
    merged_slots = merge_free_slots(all_available_slots)
    
    # Filter out slots that are too short or overlap with unavailable times
    valid_slots = []
    for start, end in merged_slots:
        slot_duration = timedelta(hours=end.hour, minutes=end.minute) - timedelta(hours=start.hour, minutes=start.minute)
        if slot_duration >= meeting_duration:
            valid_slots.append((start, end))
    
    # Check for a common slot that fits all participants
    for start, end in valid_slots:
        # Check if this slot is available for all participants
        is_valid = True
        for person, blocks in schedules.items():
            for block_start, block_end in blocks:
                block_start, block_end = map(parse_time, (block_start, block_end))
                if start < block_end and end > block_start:
                    is_valid = False
                    break
            if not is_valid:
                break
        if is_valid:
            end_time = (datetime.combine(datetime.today(), start) + meeting_duration).time()
            return f"{start.strftime('%H:%M')}-{end_time.strftime('%H:%M')}", day_of_week
    
    return None, None

# Define schedules, meeting duration, work hours, and day of the week
schedules = {
    "Olivia": [("12:30", "13:30"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Anna": [],
    "Virginia": [("9:00", "10:00"), ("11:30", "16:00"), ("16:30", "17:00")],
    "Paul": [("9:00", "9:30"), ("11:00", "11:30"), ("13:00", "14:00"), ("14:30", "16:00"), ("16:30", "17:00")]
}
meeting_duration = 1
work_start = "9:00"
work_end = "17:00"
day_of_week = "Monday"

# Find and print the meeting time
meeting_time, day = find_meeting_time(schedules, meeting_duration, work_start, work_end, day_of_week)
print(f"{meeting_time}, {day}")