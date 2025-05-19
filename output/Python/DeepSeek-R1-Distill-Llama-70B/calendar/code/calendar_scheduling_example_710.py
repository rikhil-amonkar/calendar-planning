def find_meeting_time():
    # Define the work hours
    start_time = "09:00"
    end_time = "17:00"
    
    # Define participants' busy intervals as dictionaries with name and time ranges
    participants = {
        "Cheryl": {
            "Monday": [
                ("09:00", "09:30"),
                ("11:30", "13:00"),
                ("15:30", "16:00")
            ],
            "Tuesday": [
                ("15:00", "15:30")
            ],
            "Wednesday": []
        },
        "Kyle": {
            "Monday": [
                ("09:00", "17:00")
            ],
            "Tuesday": [
                ("09:30", "17:00")
            ],
            "Wednesday": [
                ("09:00", "09:30"),
                ("10:00", "13:00"),
                ("13:30", "14:00"),
                ("14:30", "17:00")
            ]
        }
    }
    
    # Convert time strings to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hours, mins = map(int, time_str.split(':'))
        return hours * 60 + mins
    
    # Convert all busy intervals to minutes
    busy_intervals = {}
    for name, schedules in participants.items():
        busy = {}
        for day, intervals in schedules.items():
            busy_day = []
            for start, end in intervals:
                busy_start = time_to_minutes(start)
                busy_end = time_to_minutes(end)
                busy_day.append((busy_start, busy_end))
            busy[day] = busy_day
        busy_intervals[name] = busy
    
    # Define the meeting duration in minutes
    meeting_duration = 30
    
    # Generate all possible time slots within work hours
    work_start = time_to_minutes(start_time)
    work_end = time_to_minutes(end_time)
    
    # Find all available time slots for each participant
    available_slots = {}
    for name, schedules in busy_intervals.items():
        available = {}
        for day in ["Monday", "Tuesday", "Wednesday"]:
            intervals = schedules.get(day, [])
            available_day = []
            previous_end = work_start
            
            # Add available slots before the first busy interval
            if intervals and intervals[0][0] > previous_end:
                available_day.append((previous_end, intervals[0][0]))
            
            # Add available slots between busy intervals
            for i in range(1, len(intervals)):
                current_start = intervals[i-1][1]
                next_start = intervals[i][0]
                if current_start < next_start:
                    available_day.append((current_start, next_start))
            
            # Add available slots after the last busy interval
            if intervals:
                last_end = intervals[-1][1]
                if last_end < work_end:
                    available_day.append((last_end, work_end))
            else:
                # If no busy intervals, the entire work time is available
                available_day.append((work_start, work_end))
            
            available[day] = available_day
        available_slots[name] = available
    
    # Find overlapping available slots that can accommodate the meeting duration
    cheryl_available = available_slots["Cheryl"]
    kyle_available = available_slots["Kyle"]
    
    overlapping_slots = {}
    for day in ["Monday", "Tuesday", "Wednesday"]:
        cheryl_day_slots = cheryl_available.get(day, [])
        kyle_day_slots = kyle_available.get(day, [])
        
        day_overlapping = []
        for c_slot in cheryl_day_slots:
            for k_slot in kyle_day_slots:
                # Find the overlapping start and end
                start = max(c_slot[0], k_slot[0])
                end = min(c_slot[1], k_slot[1])
                
                if end - start >= meeting_duration:
                    day_overlapping.append((start, end))
        
        if day_overlapping:
            overlapping_slots[day] = day_overlapping
    
    # Find the earliest available time across all days
    earliest_time = None
    earliest_day = None
    for day in ["Monday", "Tuesday", "Wednesday"]:
        if day in overlapping_slots:
            for slot in overlapping_slots[day]:
                if earliest_time is None or slot[0] < earliest_time[0]:
                    earliest_time = slot
                    earliest_day = day
    
    # Convert the first available overlapping slot back to HH:MM format
    if earliest_time:
        meeting_start, meeting_end = earliest_time
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        meeting_start_str = minutes_to_time(meeting_start)
        meeting_end_str = minutes_to_time(meeting_end)
        return f"{meeting_start_str}:{meeting_end_str}:{earliest_day}"
    else:
        return "No available time slot found that accommodates everyone."

# Execute the function
print(find_meeting_time())