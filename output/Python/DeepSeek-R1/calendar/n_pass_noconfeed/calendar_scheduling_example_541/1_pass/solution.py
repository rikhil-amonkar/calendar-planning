def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Define work hours
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Define blocked intervals in minutes
    kayla_blocks = [
        ("10:00", "10:30"),
        ("14:30", "16:00")
    ]
    rebecca_blocks = [
        ("09:00", "13:00"),
        ("13:30", "15:00"),
        ("15:30", "16:00")
    ]
    
    # Convert all blocks to minutes
    all_blocks = []
    for start, end in kayla_blocks:
        all_blocks.append((time_to_minutes(start), time_to_minutes(end)))
    for start, end in rebecca_blocks:
        all_blocks.append((time_to_minutes(start), time_to_minutes(end)))
    
    # Sort blocks by start time
    all_blocks.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    current_start, current_end = all_blocks[0]
    for start, end in all_blocks[1:]:
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))
    
    # Find free slots between work hours
    free_slots = []
    previous_end = work_start
    
    for start, end in merged:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))
    
    # Find first free slot that can fit 60 minutes
    meeting_duration = 60
    for start_min, end_min in free_slots:
        if end_min - start_min >= meeting_duration:
            meeting_start = start_min
            meeting_end = start_min + meeting_duration
            # Format the time as HH:MM:HH:MM
            time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
            print(f"Monday:{time_str}")
            return
    
    # If no slot found (though problem states there's a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()