from datetime import datetime, timedelta

def find_meeting_time(artur_schedule, michael_schedule, day, meeting_duration):
    # Filter schedules for the given day
    artur_day_schedule = {time[0]: (time[1], time[2]) for time in artur_schedule.get(day, [])}
    michael_day_schedule = {time[0]: (time[1], time[2]) for time in michael_schedule.get(day, [])}

    # Sort schedules by start time
    artur_day_schedule = dict(sorted(artur_day_schedule.items()))
    michael_day_schedule = dict(sorted(michael_day_schedule.items()))

    # Initialize meeting time
    meeting_time = None

    # Check all possible meeting times
    for start_time in range(9, 17):
        for duration in range(30, 180, 30):
            end_time = start_time + duration

            # Convert start and end times to strings in the format HH:MM
            start_time_str = f"{start_time:02d}:{60-start_time%60:02d}"
            end_time_str = f"{end_time:02d}:{60-end_time%60:02d}"

            # Check if meeting time conflicts with anyone's schedule
            if (start_time not in artur_day_schedule or end_time <= artur_day_schedule[start_time][0]) and \
               (start_time not in michael_day_schedule or end_time <= michael_day_schedule[start_time][0]):
                # Check if meeting time is before Arthur's first meeting
                if artur_day_schedule and start_time < list(artur_day_schedule.keys())[0] or \
                   (not artur_day_schedule or artur_day_schedule.get(list(artur_day_schedule.keys())[0], (0, 0))[0] <= start_time):
                    # Check if meeting time is before Michael's first meeting
                    if michael_day_schedule and start_time < list(michael_day_schedule.keys())[0] or \
                       (not michael_day_schedule or michael_day_schedule.get(list(michael_day_schedule.keys())[0], (0, 0))[0] <= start_time):
                        # Check if meeting time is after everyone's last meeting
                        if end_time >= list(artur_day_schedule.keys())[-1] or artur_day_schedule.get(list(artur_day_schedule.keys())[-1], (0, 0))[0] >= end_time:
                            if end_time >= list(michael_day_schedule.keys())[-1] or michael_day_schedule.get(list(michael_day_schedule.keys())[-1], (0, 0))[0] >= end_time:
                                # Meeting time found
                                meeting_time = (day, start_time_str, end_time_str)
                                return meeting_time

    # If no meeting time is found, return None
    return None


# Define schedules
artur_schedule = {
    "Monday": [(11, 30, 0), (13, 30, 0), (15, 30, 0)],
    "Tuesday": [(13, 30, 0), (16, 30, 0)],
    "Wednesday": [(10, 30, 0), (11, 30, 0), (12, 30, 0), (14, 30, 0), (16, 30, 0)]
}

michael_schedule = {
    "Monday": [(9, 0, 0), (12, 0, 0), (14, 30, 0), (15, 0, 0)],
    "Tuesday": [(9, 30, 0), (12, 30, 0), (14, 30, 0)],
    "Wednesday": [(10, 0, 0), (13, 30, 0)]
}

# Define meeting duration
meeting_duration = 30

# Define day
day = "Monday"

# Find meeting time
meeting_time = find_meeting_time(artur_schedule, michael_schedule, day, meeting_duration)

# Print meeting time
if meeting_time:
    print(f"Meeting time: {meeting_time[1]} - {meeting_time[2]} on {meeting_time[0]}")
else:
    print("No meeting time found")