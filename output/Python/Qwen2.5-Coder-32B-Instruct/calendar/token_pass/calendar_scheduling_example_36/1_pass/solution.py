from datetime import datetime, timedelta

def find_meeting_time(ryan_busy, ruth_busy, denise_busy, meeting_duration, work_start, work_end, denise_preference_end):
    # Convert times to datetime objects
    work_start = datetime.strptime(work_start, '%H:%M')
    work_end = datetime.strptime(work_end, '%H:%M')
    denise_preference_end = datetime.strptime(denise_preference_end, '%H:%M')
    
    # Generate all possible 30-minute slots within work hours
    current_time = work_start
    all_slots = []
    while current_time + timedelta(minutes=meeting_duration) <= work_end:
        all_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        current_time += timedelta(minutes=30)
    
    # Function to convert busy times to datetime objects and remove them from all slots
    def get_free_slots(busy_times):
        busy_times = [(datetime.strptime(start, '%H:%M'), datetime.strptime(end, '%H:%M')) for start, end in busy_times]
        free_slots = []
        last_end = work_start
        
        for start, end in sorted(busy_times):
            if last_end < start:
                free_slots.append((last_end, start))
            last_end = max(last_end, end)
        
        if last_end < work_end:
            free_slots.append((last_end, work_end))
        
        return free_slots
    
    # Get free slots for each person
    ryan_free = get_free_slots(ryan_busy)
    ruth_free = get_free_slots(ruth_busy)
    denise_free = get_free_slots(denise_busy)
    
    # Convert free slots to sets of 30-minute intervals
    def slots_to_intervals(free_slots):
        intervals = set()
        for start, end in free_slots:
            current = start
            while current + timedelta(minutes=meeting_duration) <= end:
                intervals.add((current, current + timedelta(minutes=meeting_duration)))
                current += timedelta(minutes=30)
        return intervals
    
    ryan_intervals = slots_to_intervals(ryan_free)
    ruth_intervals = slots_to_intervals(ruth_free)
    denise_intervals = slots_to_intervals(denise_free)
    
    # Find common intervals
    common_intervals = ryan_intervals.intersection(ruth_intervals).intersection(denise_intervals)
    
    # Filter intervals based on additional constraints
    valid_intervals = [interval for interval in common_intervals if interval[1] <= denise_preference_end]
    
    # Select the first valid interval
    if valid_intervals:
        selected_interval = valid_intervals[0]
        start_time = selected_interval[0].strftime('%H:%M')
        end_time = selected_interval[1].strftime('%H:%M')
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No valid time slot found")

# Input data
ryan_busy = [('9:00', '9:30'), ('12:30', '13:00')]
ruth_busy = []
denise_busy = [('9:30', '10:30'), ('12:00', '13:00'), ('14:30', '16:30')]
meeting_duration = 60  # in minutes
work_start = '9:00'
work_end = '17:00'
denise_preference_end = '12:30'

# Find and print the meeting time
find_meeting_time(ryan_busy, ruth_busy, denise_busy, meeting_duration, work_start, work_end, denise_preference_end)