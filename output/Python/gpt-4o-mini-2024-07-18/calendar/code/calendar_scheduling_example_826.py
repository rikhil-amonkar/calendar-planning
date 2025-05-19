from datetime import datetime, timedelta

def find_meeting_time():
    # Define participants' availability
    cheryl_availability = {
        "Monday": [(9, 0), (17, 0)],
        "Tuesday": [(9, 0), (17, 0)],
        "Wednesday": [(9, 0), (17, 0)],
        "Thursday": [(9, 0), (17, 0)],
    }
    
    james_availability = {
        "Monday": [(9, 30), (10, 30), (11, 0), (12, 30), (13, 0), (14, 30), (15, 30), (16, 30), (17, 0)],
        "Tuesday": [(9, 0), (11, 0), (11, 30), (12, 30), (15, 30), (16, 0), (17, 0)],
        "Wednesday": [(10, 0), (11, 0), (12, 0), (13, 0), (16, 0), (16, 30), (17, 0)],
        "Thursday": [(9, 30), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (16, 30), (17, 0)],
    }

    meeting_duration = timedelta(minutes=30)

    for day in ["Monday", "Tuesday", "Thursday"]:  # Excluding Wednesday
        available_slots = []
        
        # Cheryl's available time
        cheryl_start, cheryl_end = cheryl_availability[day][0]
        cheryl_start_time = datetime.now().replace(hour=cheryl_start, minute=cheryl_end, second=0)

        # Generate free slots for James on that day
        james_intervals = []
        last_end_time = cheryl_start_time

        for start_hour, start_minute in james_availability[day]:
            current_start_time = datetime.now().replace(hour=start_hour, minute=start_minute, second=0)
            if current_start_time >= last_end_time + meeting_duration:
                available_slots.append((last_end_time, current_start_time))
            last_end_time = current_start_time

        # End of day (Cheryl's available time)
        end_of_day = datetime.now().replace(hour=17, minute=0, second=0)
        if end_of_day >= last_end_time + meeting_duration:
            available_slots.append((last_end_time, end_of_day))

        # Look for a suitable slot of at least 30 mins for both
        for start, end in available_slots:
            if end - start >= meeting_duration:
                proposed_start_time = start
                proposed_end_time = proposed_start_time + meeting_duration
                return f"{proposed_start_time.strftime('%H:%M')}:{proposed_end_time.strftime('%H:%M')} {day}"

# Call the function to find a meeting time
print(find_meeting_time())