def merge_intervals(intervals):
    # Sort intervals by start time
    intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    for current in intervals:
        if not merged:
            merged.append(current)
        else:
            last_start, last_end = merged[-1]
            if current[0] <= last_end:
                merged[-1] = (last_start, max(last_end, current[1]))
            else:
                merged.append(current)
    return merged

def minutes_to_time(minutes):
    # Convert minutes (from midnight) to an HH:MM string
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def find_meeting_slot(busy_intervals, work_start, work_end, duration):
    # Merge all busy intervals
    merged_busy = merge_intervals(busy_intervals)
    
    free_intervals = []
    # Check free time before the first busy interval
    if work_start < merged_busy[0][0]:
        free_intervals.append((work_start, merged_busy[0][0]))
    
    # Check free times between merged busy intervals
    for i in range(len(merged_busy) - 1):
        free_start = merged_busy[i][1]
        free_end = merged_busy[i+1][0]
        if free_end - free_start > 0:
            free_intervals.append((free_start, free_end))
    
    # Check free time after the last busy interval
    if merged_busy[-1][1] < work_end:
        free_intervals.append((merged_busy[-1][1], work_end))
    
    # Return the first free slot that fits the meeting duration
    for start, end in free_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    meeting_duration = 30  # Duration in minutes
    # Define working hours (using minutes relative to 9:00)
    work_start = 0         # 9:00
    work_end = 480         # 17:00 (9:00 + 480 minutes = 17:00)
    
    # Busy intervals for each participant (times are minutes relative to 9:00)
    busy_intervals = [
        # Megan
        (0, 30),    # 9:00-9:30
        (60, 120),  # 10:00-11:00
        (180, 210), # 12:00-12:30
        
        # Christine
        (0, 30),    # 9:00-9:30
        (150, 180), # 11:30-12:00
        (240, 300), # 13:00-14:00
        (390, 450), # 15:30-16:30
        
        # Gabriel has no meetings (free all day)
        
        # Sara
        (150, 180), # 11:30-12:00
        (330, 360), # 14:30-15:00
        
        # Bruce
        (30, 60),   # 9:30-10:00
        (90, 180),  # 10:30-12:00
        (210, 300), # 12:30-14:00
        (330, 360), # 14:30-15:00
        (390, 450), # 15:30-16:30
        
        # Kathryn
        (60, 390),  # 10:00-15:30
        (420, 450), # 16:00-16:30
        
        # Billy
        (0, 30),    # 9:00-9:30
        (120, 150), # 11:00-11:30
        (180, 300), # 12:00-14:00
        (330, 390)  # 14:30-15:30
    ]
    
    # Find a free slot that can accommodate a 30-minute meeting.
    slot = find_meeting_slot(busy_intervals, work_start, work_end, meeting_duration)
    if slot:
        slot_start, slot_end = slot
        # Our times are relative to 9:00, so add 9*60 minutes to convert to minutes from midnight.
        base = 9 * 60
        start_str = minutes_to_time(base + slot_start)
        end_str = minutes_to_time(base + slot_end)
        day = "Monday"
        # Output format: day HH:MM:HH:MM (e.g., Monday 16:30:17:00)
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()