def find_earliest_available_slot(busy, work_start, work_end):
    # Convert each busy time to minutes since work_start (9:00)
    busy_converted = []
    for time in busy:
        start_str, end_str = time
        start = int(start_str.split(':')[0]) * 60 + int(start_str.split(':')[1])
        end = int(end_str.split(':')[0]) * 60 + int(end_str.split(':')[1])
        start_work = start - 9 * 60  # Convert to minutes since 9:00
        end_work = end - 9 * 60
        busy_converted.append((start_work, end_work))
    
    # Sort the busy intervals by their start time
    busy_converted.sort(key=lambda x: x[0])
    
    # Calculate the gaps between busy intervals
    gaps = []
    
    # Check before the first busy interval
    if busy_converted[0][0] > 0:
        gaps.append((0, busy_converted[0][0]))
    
    # Check between each pair of consecutive busy intervals
    for i in range(len(busy_converted) - 1):
        current_end = busy_converted[i][1]
        next_start = busy_converted[i + 1][0]
        if next_start > current_end:
            gaps.append((current_end, next_start))
    
    # Check after the last busy interval
    last_end = busy_converted[-1][1]
    if last_end < work_end:
        gaps.append((last_end, work_end))
    
    # Find the earliest 30-minute slot
    for gap in gaps:
        start_gap, end_gap = gap
        available_time = end_gap - start_gap
        if available_time >= 30:
            slot_start = start_gap
            slot_end = slot_start + 30
            if slot_end > work_end:
                continue  # Slot ends after work hours
            # Format the slot into the required string
            hours = slot_start // 60
            minutes = slot_start % 60
            return f"Monday, {hours:02d}:{minutes:02d} - {hours:02d}:{minutes + 30:02d}"
    
    # If no slot found (shouldn't happen as work hours are 8 hours and busy times are within)
    return "No slot found"

# Read input
busy_times = [
    ("9:00", "9:30"),
    ("10:30", "12:00"),
    ("12:30", "13:30"),
    ("14:00", "14:30"),
    ("15:00", "16:30")
]

# Work hours are from 9:00 to 17:00 (480 minutes)
work_start = 0  # 9:00 is 0 minutes
work_end = 480  # 17:00 is 480 minutes

# Find and print the earliest available slot
result = find_earliest_available_slot(busy_times, work_start, work_end)
print(result)
