def find_meeting_time():
    # Define the schedules for each participant as dictionaries with their busy intervals
    schedules = {
        'Gary': {
            'Monday': [(9*60 + 30, 10*60), (11*60, 13*60), (14*60, 14*60 + 30), (16*60 + 30, 17*60)],
            'Tuesday': [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (14*60 + 30, 16*60)]
        },
        'David': {
            'Monday': [(9*60, 9*60 + 30), (10*60, 13*60), (14*60 + 30, 16*60 + 30)],
            'Tuesday': [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 12*60 + 30), 
                        (13*60, 14*60 + 30), (15*60, 16*60), (16*60 + 30, 17*60)]
        }
    }

    # Convert time ranges to minutes since midnight for easier comparison
    def time_to_minutes(hours, minutes):
        return hours * 60 + minutes

    # Generate all possible 60-minute time slots between 9:00 and 17:00
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    time_slots = []
    for t in range(start_time, end_time - 60, 30):
        time_slots.append((t, t + 60))

    # Check each time slot against both participants' schedules
    for day in ['Monday', 'Tuesday']:
        for slot in time_slots:
            start, end = slot
            gary_available = True
            for busy_start, busy_end in schedules['Gary'][day]:
                if not (end <= busy_start or start >= busy_end):
                    gary_available = False
                    break
            if not gary_available:
                continue

            david_available = True
            for busy_start, busy_end in schedules['David'][day]:
                if not (end <= busy_start or start >= busy_end):
                    david_available = False
                    break
            if david_available:
                # Convert the time slot back to HH:MM format
                hours_start = start // 60
                minutes_start = start % 60
                hours_end = end // 60
                minutes_end = end % 60
                return f"The proposed meeting time is {hours_start:02d}:{minutes_start:02d}:{hours_end:02d}:{minutes_end:02d} on {day}."

    # If no time slot found (though the problem states there is a solution)
    return "No available time slot found"

# Execute the function
meeting_time = find_meeting_time()
print(meeting_time)