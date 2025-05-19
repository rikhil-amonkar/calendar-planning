def find_meeting_time():
    # Define the schedules for each participant
    daniel_schedule = {
        "Monday": [(9, 30, 10, 30), (12, 0, 12, 30), (13, 0, 14, 0), (14, 30, 15, 0), (15, 30, 16, 0)],
        "Tuesday": [(11, 0, 12, 0), (13, 0, 13, 30), (15, 30, 16, 0), (16, 30, 17, 0)],
        "Wednesday": [(9, 0, 10, 0), (14, 0, 14, 30)],
        "Thursday": [(10, 30, 11, 0), (12, 0, 13, 0), (14, 30, 15, 0), (15, 30, 16, 0)],
        "Friday": [(9, 0, 9, 30), (11, 30, 12, 0), (13, 0, 13, 30), (16, 30, 17, 0)]
    }

    bradley_schedule = {
        "Monday": [(9, 30, 11, 0), (11, 30, 12, 0), (12, 30, 13, 0), (14, 0, 15, 0)],
        "Tuesday": [(10, 30, 11, 0), (12, 0, 13, 0), (13, 30, 14, 0), (15, 30, 16, 30)],
        "Wednesday": [(9, 0, 10, 0), (11, 0, 13, 0), (13, 30, 14, 0), (14, 30, 17, 0)],
        "Thursday": [(9, 0, 12, 30), (13, 30, 14, 0), (14, 30, 15, 0), (15, 30, 16, 30)],
        "Friday": [(9, 0, 9, 30), (10, 0, 12, 30), (13, 0, 13, 30), (14, 0, 14, 30), (15, 30, 16, 30)]
    }

    # Preferences
    daniel_preferences = ["Tuesday", "Friday"]  # Days Daniel prefers not to meet
    bradley_preferences = ["Monday", "Friday"]  # Days Bradley prefers not to meet
    bradley_tuesday_before_12 = False  # Bradley does not want to meet on Tuesday before 12:00

    # Convert time ranges to minutes since midnight for easier calculations
    def time_to_minutes(hours, minutes):
        return hours * 60 + minutes

    # Define the possible days, considering preferences
    possible_days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    possible_days = [day for day in possible_days if day not in daniel_preferences and day not in bradley_preferences]

    # Iterate through each possible day
    for day in possible_days:
        # Get both schedules for the day
        daniel_schedule_day = daniel_schedule[day]
        bradley_schedule_day = bradley_schedule[day]

        # Combine and sort all busy intervals
        all_busy = daniel_schedule_day + bradley_schedule_day
        all_busy.sort(key=lambda x: (x[0], x[1]))

        # Check each possible time slot
        start_time = 9 * 60  # 9:00 in minutes
        end_time = 17 * 60   # 17:00 in minutes

        # Iterate through each 30-minute slot
        while start_time < end_time:
            current_end = start_time + 30
            if current_end > end_time:
                current_end = end_time

            # Convert start and end times back to HH:MM format
            start_hh, start_mm = divmod(start_time, 60)
            end_hh, end_mm = divmod(current_end, 60)

            # Check if this time slot works for everyone
            works_for_all = True
            for schedule in [daniel_schedule_day, bradley_schedule_day]:
                for meeting in schedule:
                    meeting_start = time_to_minutes(meeting[0], meeting[1])
                    meeting_end = time_to_minutes(meeting[2], meeting[3])

                    # Check overlap
                    if not (current_end <= meeting_start or start_time >= meeting_end):
                        works_for_all = False
                        break
                if not works_for_all:
                    break

            if works_for_all:
                # Additional preference checks
                if day == "Tuesday" and start_time < 12 * 60:
                    continue  # Bradley does not want to meet on Tuesday before 12:00
                return f"{day}: {start_hh:02d}:{start_mm:02d}-{end_hh:02d}:{end_mm:02d}"

            start_time += 30  # Move to the next 30-minute slot

    # If no time found (should not happen as per problem statement)
    return "No available time found"

# Execute the function
print(find_meeting_time())