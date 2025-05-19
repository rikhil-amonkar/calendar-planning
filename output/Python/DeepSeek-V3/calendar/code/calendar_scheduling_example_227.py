def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Convert each participant's busy slots to minutes
    # Natalie: free all day
    natalie_busy = []
    
    # David: busy 11:30-12:00, 14:30-15:00; prefers after 14:00
    david_busy = [(11 * 60 + 30, 12 * 60), (14 * 60 + 30, 15 * 60)]
    david_preference = 14 * 60  # prefers after 14:00
    
    # Douglas: busy 9:30-10:00, 11:30-12:00, 13:00-13:30, 14:30-15:00
    douglas_busy = [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60),
                    (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60)]
    
    # Ralph: busy 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:30-15:00, 15:30-16:00, 16:30-17:00
    ralph_busy = [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60),
                  (11 * 60 + 30, 12 * 60 + 30), (13 * 60 + 30, 15 * 60),
                  (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
    
    # Jordan: busy 9:00-10:00, 12:00-12:30, 13:00-13:30, 14:30-15:00, 15:30-17:00
    jordan_busy = [(9 * 60, 10 * 60), (12 * 60, 12 * 60 + 30),
                   (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60),
                   (15 * 60 + 30, 17 * 60)]
    
    # Combine all busy slots
    all_busy = david_busy + douglas_busy + ralph_busy + jordan_busy
    
    # Sort busy slots by start time
    all_busy.sort()
    
    # Find free slots by checking gaps between busy slots
    free_slots = []
    previous_end = work_start
    
    for start, end in all_busy:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    # Check the end of the day
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))
    
    # Filter free slots that are at least 30 minutes and meet David's preference
    meeting_duration = 30
    valid_slots = []
    
    for start, end in free_slots:
        if end - start >= meeting_duration and start >= david_preference:
            valid_slots.append((start, end))
    
    # Select the earliest valid slot
    if valid_slots:
        meeting_start = valid_slots[0][0]
        meeting_end = meeting_start + meeting_duration
    else:
        return "No suitable time found."
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = minutes_to_time(meeting_start)
    end_time = minutes_to_time(meeting_end)
    
    return f"{start_time}:{end_time}", "Monday"

# Run the function and print the result
time_range, day = find_meeting_time()
print(f"{time_range} {day}")