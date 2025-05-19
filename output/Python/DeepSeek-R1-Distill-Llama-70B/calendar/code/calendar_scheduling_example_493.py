def find_meeting_time():
    # Define the work hours
    start_time = "09:00"
    end_time = "17:00"
    
    # Define participants' busy intervals as dictionaries with name and time ranges
    participants = {
        "Tyler": [],
        "Kelly": [],
        "Stephanie": [
            ("11:00", "11:30"),
            ("14:30", "15:00")
        ],
        "Hannah": [],
        "Joe": [
            ("09:00", "09:30"),
            ("10:00", "12:00"),
            ("12:30", "13:00"),
            ("14:00", "17:00")
        ],
        "Diana": [
            ("09:00", "10:30"),
            ("11:30", "12:00"),
            ("13:00", "14:00"),
            ("14:30", "15:30"),
            ("16:00", "17:00")
        ],
        "Deborah": [
            ("09:00", "10:00"),
            ("10:30", "12:00"),
            ("12:30", "13:00"),
            ("13:30", "14:00"),
            ("14:30", "15:30"),
            ("16:00", "16:30")
        ]
    }
    
    # Convert time strings to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hours, mins = map(int, time_str.split(':'))
        return hours * 60 + mins
    
    # Convert all busy intervals to minutes
    busy_intervals = {}
    for name, intervals in participants.items():
        busy = []
        for start, end in intervals:
            busy_start = time_to_minutes(start)
            busy_end = time_to_minutes(end)
            busy.append((busy_start, busy_end))
        busy_intervals[name] = busy
    
    # Define the meeting duration in minutes
    meeting_duration = 30
    
    # Generate all possible time slots within work hours
    work_start = time_to_minutes(start_time)
    work_end = time_to_minutes(end_time)
    
    # Find all available time slots for each participant
    available_slots = {}
    for name, intervals in busy_intervals.items():
        available = []
        previous_end = work_start
        
        # Add available slots before the first busy interval
        if intervals and intervals[0][0] > previous_end:
            available.append((previous_end, intervals[0][0]))
        
        # Add available slots between busy intervals
        for i in range(1, len(intervals)):
            current_start = intervals[i-1][1]
            next_start = intervals[i][0]
            if current_start < next_start:
                available.append((current_start, next_start))
        
        # Add available slots after the last busy interval
        if intervals:
            last_end = intervals[-1][1]
            if last_end < work_end:
                available.append((last_end, work_end))
        else:
            # If no busy intervals, the entire work time is available
            available.append((work_start, work_end))
        
        available_slots[name] = available
    
    # Find overlapping available slots that can accommodate the meeting duration
    tyler_available = available_slots["Tyler"]
    kelly_available = available_slots["Kelly"]
    stephanie_available = available_slots["Stephanie"]
    hannah_available = available_slots["Hannah"]
    joe_available = available_slots["Joe"]
    diana_available = available_slots["Diana"]
    deborah_available = available_slots["Deborah"]
    
    overlapping_slots = []
    for t_slot in tyler_available:
        for k_slot in kelly_available:
            for s_slot in stephanie_available:
                for h_slot in hannah_available:
                    for j_slot in joe_available:
                        for d_slot in diana_available:
                            for de_slot in deborah_available:
                                # Find the overlapping start and end
                                start = max(t_slot[0], k_slot[0], s_slot[0], h_slot[0], j_slot[0], d_slot[0], de_slot[0])
                                end = min(t_slot[1], k_slot[1], s_slot[1], h_slot[1], j_slot[1], d_slot[1], de_slot[1])
                                
                                if end - start >= meeting_duration:
                                    overlapping_slots.append((start, end))
    
    # Convert the first available overlapping slot back to HH:MM format
    if overlapping_slots:
        meeting_start, meeting_end = overlapping_slots[0]
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        meeting_start_str = minutes_to_time(meeting_start)
        meeting_end_str = minutes_to_time(meeting_end)
        day = "Monday"
        return f"{meeting_start_str}:{meeting_end_str}:{day}"
    else:
        return "No available time slot found that accommodates everyone."

# Execute the function
print(find_meeting_time())