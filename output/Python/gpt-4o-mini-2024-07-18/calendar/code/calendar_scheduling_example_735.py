from datetime import datetime, timedelta

# Function to find common available slots for a meeting
def find_meeting_time(ronald_schedule, amber_schedule, duration):
    # Define work hours
    work_days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 AM in minutes
    work_end = 17 * 60    # 5:00 PM in minutes

    # Prepare a list to check available slots
    available_slots = []
    
    for day in work_days:
        ronald_free_times = get_free_times(ronald_schedule[day], work_start, work_end)
        amber_free_times = get_free_times(amber_schedule[day], work_start, work_end)

        # Find common free time slots
        common_free_times = find_common_availability(ronald_free_times, amber_free_times, duration)

        if common_free_times:
            available_slots.extend((day, slot) for slot in common_free_times)

    return available_slots[0] if available_slots else None

def get_free_times(schedule, work_start, work_end):
    # Convert blocked times into available times
    free_times = []
    last_end = work_start
    
    for start, end in sorted(schedule):
        if start > last_end:
            free_times.append((last_end, start))
        last_end = max(last_end, end)
    
    if last_end < work_end:
        free_times.append((last_end, work_end))
    
    return free_times

def find_common_availability(free_times1, free_times2, duration):
    common_times = []
    
    for start1, end1 in free_times1:
        for start2, end2 in free_times2:
            common_start = max(start1, start2)
            common_end = min(end1, end2)
            
            if (common_end - common_start) >= duration:
                common_times.append((common_start, common_start + duration))

    return common_times

# Ronald and Amber's schedules
ronald_schedule = {
    'Monday': [(630, 630 + 30), (720, 720 + 30), (930, 930 + 30)],
    'Tuesday': [(540, 540 + 30), (720, 720 + 30), (930, 930 + 60)],
    'Wednesday': [(570, 630), (660, 780)],
}

amber_schedule = {
    'Monday': [(540, 550), (600, 630), (750, 780), (840, 870)],
    'Tuesday': [(540, 550), (600, 690), (720, 750)],
    'Wednesday': [(540, 550), (600, 630), (660, 810)],
}

# Duration of the meeting in minutes
meeting_duration = 30

meeting_time = find_meeting_time(ronald_schedule, amber_schedule, meeting_duration)

if meeting_time:
    day, time_slot = meeting_time
    start_time = (time_slot[0] // 60, time_slot[0] % 60)
    print(f"{day}: {start_time[0]:02}:{start_time[1]:02} - {start_time[0]:02}:{start_time[1] + meeting_duration:02}")