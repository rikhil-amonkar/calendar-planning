def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration, days):
    for day in days:
        # Initialize available time for the day
        available_start = work_hours_start
        available_end = work_hours_end
        
        # Collect all busy times for the day for all participants
        busy_times = []
        for participant in participants_schedules:
            if day in participant:
                busy_times.extend(participant[day])
        
        # Sort busy times by start time
        busy_times.sort()
        
        # Find available slots
        current_time = available_start
        for busy_start, busy_end in busy_times:
            if busy_start > current_time:
                # Check if the slot is long enough
                if busy_start - current_time >= meeting_duration:
                    return day, (current_time, current_time + meeting_duration)
            # Update current_time to the end of the busy slot
            if busy_end > current_time:
                current_time = busy_end
        
        # Check the remaining time after the last busy slot
        if available_end - current_time >= meeting_duration:
            return day, (current_time, current_time + meeting_duration)
    
    return None, None

def main():
    # Define participants' schedules
    patricia_schedule = {
        'Monday': [(10.0, 10.5), (11.5, 12.0), (13.0, 13.5), (14.5, 15.5), (16.0, 16.5)],
        'Tuesday': [(10.0, 10.5), (11.0, 12.0), (14.0, 16.0), (16.5, 17.0)]
    }
    
    jesse_schedule = {
        'Monday': [(9.0, 17.0)],
        'Tuesday': [(11.0, 11.5), (12.0, 12.5), (13.0, 14.0), (14.5, 15.0), (15.5, 17.0)]
    }
    
    participants_schedules = [patricia_schedule, jesse_schedule]
    
    # Define meeting constraints
    work_hours_start = 9.0
    work_hours_end = 17.0
    meeting_duration = 1.0
    days = ['Monday', 'Tuesday']
    
    # Find meeting time
    day, time_range = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration, days)
    
    if day and time_range:
        start_hour = int(time_range[0])
        start_min = int((time_range[0] - start_hour) * 60)
        end_hour = int(time_range[1])
        end_min = int((time_range[1] - end_hour) * 60)
        
        print(f"{day}, {{{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}}}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()