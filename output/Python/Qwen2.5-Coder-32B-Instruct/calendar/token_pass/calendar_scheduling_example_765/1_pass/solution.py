def find_meeting_time(joshua_schedule, joyce_schedule, meeting_duration, preferred_times):
    # Define the work hours
    start_time = 9 * 60  # 9:00 AM in minutes
    end_time = 17 * 60   # 5:00 PM in minutes
    
    # Function to convert time in minutes to HH:MM format
    def time_to_str(minutes):
        return f"{minutes // 60:02}:{minutes % 60:02}"
    
    # Function to find free slots for a person
    def find_free_slots(busy_times, start, end):
        free_slots = []
        current_start = start
        for busy_start, busy_end in sorted(busy_times):
            if busy_start > current_start:
                free_slots.append((current_start, busy_start))
            current_start = max(current_start, busy_end)
        if current_start < end:
            free_slots.append((current_start, end))
        return free_slots
    
    # Days of the week and their respective busy times
    days = ['Monday', 'Tuesday', 'Wednesday']
    joshua_busy = {
        'Monday': [(15*60, 15*60+30)],
        'Tuesday': [(11*60+30, 12*60), (13*60, 13*60+30), (14*60+30, 15*60)],
        'Wednesday': []
    }
    joyce_busy = {
        'Monday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60+30), (13*60, 15*60), (15*60+30, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 9*60+30), (10*60, 11*60), (12*60+30, 15*60), (16*60, 16*60+30)]
    }
    
    # Iterate over each day to find a suitable meeting time
    for day in days:
        joshua_free_slots = find_free_slots(joshua_busy.get(day, []), start_time, end_time)
        joyce_free_slots = find_free_slots(joyce_busy.get(day, []), start_time, end_time)
        
        # Find overlapping free slots
        i, j = 0, 0
        while i < len(joshua_free_slots) and j < len(joyce_free_slots):
            joshua_start, joshua_end = joshua_free_slots[i]
            joyce_start, joyce_end = joyce_free_slots[j]
            
            overlap_start = max(joshua_start, joyce_start)
            overlap_end = min(joshua_end, joyce_end)
            
            if overlap_end - overlap_start >= meeting_duration:
                # Check preferred times
                if day == 'Monday' and overlap_start < 12*60:
                    i += 1
                    continue
                
                # Found a suitable time slot
                meeting_start = time_to_str(overlap_start)
                meeting_end = time_to_str(overlap_start + meeting_duration)
                return f"{meeting_start}:{meeting_end} {day}"
            
            # Move to the next slot
            if joshua_end < joyce_end:
                i += 1
            else:
                j += 1
    
    # If no suitable time is found (though the problem guarantees one exists)
    return "No suitable time found"

# Given data
joshua_schedule = {
    'Monday': [(15, 15.5)],
    'Tuesday': [(11.5, 12), (13, 13.5), (14.5, 15)],
    'Wednesday': []
}
joyce_schedule = {
    'Monday': [(9, 9.5), (10, 11), (11.5, 12.5), (13, 15), (15.5, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 9.5), (10, 11), (12.5, 15), (16, 16.5)]
}
meeting_duration = 30  # in minutes
preferred_times = {'Monday': 12*60}

# Find and print the meeting time
print(find_meeting_time(joshua_schedule, joyce_schedule, meeting_duration, preferred_times))