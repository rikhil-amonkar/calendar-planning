from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Function to merge busy times into a single list and sort it
    def merge_and_sort_busy_times(busy_times):
        merged_times = []
        for start, end in busy_times:
            start = datetime.strptime(start, "%H:%M")
            end = datetime.strptime(end, "%H:%M")
            merged_times.append((start, end))
        merged_times.sort()
        return merged_times
    
    # Function to find free slots for a given person
    def find_free_slots(busy_times, work_start, work_end):
        free_slots = []
        current_time = work_start
        
        for start, end in busy_times:
            if current_time < start:
                free_slots.append((current_time, start))
            current_time = max(current_time, end)
        
        if current_time < work_end:
            free_slots.append((current_time, work_end))
        
        return free_slots
    
    # Merge and sort busy times for all people
    merged_busy_times = {}
    for person, busy_times in schedules.items():
        merged_busy_times[person] = merge_and_sort_busy_times(busy_times)
    
    # Find free slots for each person
    free_slots_per_person = {}
    for person, busy_times in merged_busy_times.items():
        free_slots_per_person[person] = find_free_slots(busy_times, work_start, work_end)
    
    # Find common free slots
    common_free_slots = free_slots_per_person[next(iter(free_slots_per_person))]
    for person, free_slots in free_slots_per_person.items():
        new_common_slots = []
        for start1, end1 in common_free_slots:
            for start2, end2 in free_slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_start < overlap_end:
                    new_common_slots.append((overlap_start, overlap_end))
        common_free_slots = new_common_slots
    
    # Find the first common slot that fits the meeting duration
    for start, end in common_free_slots:
        if end - start >= meeting_duration:
            return f"{start.strftime('%H:%M')}-{(start + meeting_duration).strftime('%H:%M')}", "Monday"
    
    return None, None

# Schedules in the format of (start, end) times
schedules = {
    "Adam": [("09:30", "10:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Roy": [("10:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("16:30", "17:00")]
}

meeting_time, day_of_week = find_meeting_time(schedules, 30, "09:00", "17:00")
print(f"Meeting Time: {meeting_time}, Day of Week: {day_of_week}")