def find_meeting_time(participants_schedules, day, work_hours, duration):
    start_work, end_work = work_hours
    busy_times = []
    
    # Collect all busy times for each participant
    for schedule in participants_schedules:
        busy_times.extend(schedule)
    
    # Sort all busy times by start time
    busy_times.sort()
    
    # Find free slots by checking gaps between busy times
    free_slots = []
    previous_end = start_work
    
    for start, end in busy_times:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    # Check the slot after the last busy time
    if previous_end < end_work:
        free_slots.append((previous_end, end_work))
    
    # Merge overlapping or adjacent busy times (not needed here as we process all at once)
    # Now find the first free slot that can fit the duration
    for slot_start, slot_end in free_slots:
        if (slot_end - slot_start) >= duration:
            return (slot_start, slot_start + duration)
    
    return None

def main():
    # Define participants' schedules in 24-hour format as (start, end) tuples in minutes since 9:00 (540)
    # Convert all times to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    # Participants' schedules in (start, end) in minutes since midnight
    andrea = []
    jack = [(time_to_minutes('9:00'), time_to_minutes('9:30')), (time_to_minutes('14:00'), time_to_minutes('14:30'))]
    madison = [(time_to_minutes('9:30'), time_to_minutes('10:30')), (time_to_minutes('13:00'), time_to_minutes('14:00')), 
               (time_to_minutes('15:00'), time_to_minutes('15:30')), (time_to_minutes('16:30'), time_to_minutes('17:00'))]
    rachel = [(time_to_minutes('9:30'), time_to_minutes('10:30')), (time_to_minutes('11:00'), time_to_minutes('11:30')), 
              (time_to_minutes('12:00'), time_to_minutes('13:30')), (time_to_minutes('14:30'), time_to_minutes('15:30')), 
              (time_to_minutes('16:00'), time_to_minutes('17:00'))]
    douglas = [(time_to_minutes('9:00'), time_to_minutes('11:30')), (time_to_minutes('12:00'), time_to_minutes('16:30'))]
    ryan = [(time_to_minutes('9:00'), time_to_minutes('9:30')), (time_to_minutes('13:00'), time_to_minutes('14:00')), 
            (time_to_minutes('14:30'), time_to_minutes('17:00'))]
    
    participants_schedules = [andrea, jack, madison, rachel, douglas, ryan]
    day = "Monday"
    work_hours = (time_to_minutes('9:00'), time_to_minutes('17:00'))
    duration = 30  # minutes
    
    # Find the meeting time
    meeting_time = find_meeting_time(participants_schedules, day, work_hours, duration)
    
    if meeting_time:
        start, end = meeting_time
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"{start_time}:{end_time}:{day}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()