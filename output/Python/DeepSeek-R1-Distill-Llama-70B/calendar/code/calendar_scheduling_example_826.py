def find_meeting_time():
    # Define the schedules for each participant as dictionaries with their busy intervals
    schedules = {
        'Cheryl': {
            'Monday': [],
            'Tuesday': [],
            'Wednesday': [],
            'Thursday': []
        },
        'James': {
            'Monday': [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (12*60 + 30, 13*60), 
                       (14*60 + 30, 15*60 + 30), (16*60 + 30, 17*60)],
            'Tuesday': [(9*60, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 15*60 + 30), 
                        (16*60, 17*60)],
            'Wednesday': [(10*60, 11*60), (12*60, 13*60), (13*60 + 30, 16*60)],
            'Thursday': [(9*60 + 30, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 13*60 + 30),
                         (14*60, 14*60 + 30), (16*60 + 30, 17*60)]
        }
    }

    # Generate all possible 30-minute time slots between 9:00 and 17:00
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    time_slots = []
    for t in range(start_time, end_time - 30, 30):
        time_slots.append((t, t + 30))

    # Check each time slot against both participants' schedules, starting with Monday and Tuesday
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday']:
        for slot in time_slots:
            start, end = slot
            cheryl_available = True
            for busy_start, busy_end in schedules['Cheryl'][day]:
                if not (end <= busy_start or start >= busy_end):
                    cheryl_available = False
                    break
            if not cheryl_available:
                continue

            james_available = True
            for busy_start, busy_end in schedules['James'][day]:
                if not (end <= busy_start or start >= busy_end):
                    james_available = False
                    break
            if james_available:
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