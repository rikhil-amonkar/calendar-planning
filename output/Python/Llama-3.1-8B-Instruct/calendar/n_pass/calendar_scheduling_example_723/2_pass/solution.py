from datetime import datetime, timedelta

def find_meeting_time(artur_schedule, michael_schedule, day, meeting_duration):
    # Filter schedules for the given day
    artur_day_schedule = {time: duration for time, duration in artur_schedule.items() if time[0] == day}
    michael_day_schedule = {time: duration for time, duration in michael_schedule.items() if time[0] == day}

    # Sort schedules by start time
    artur_day_schedule = dict(sorted(artur_day_schedule.items()))
    michael_day_schedule = dict(sorted(michael_day_schedule.items()))

    # Initialize meeting time
    meeting_time = None

    # Check all possible meeting times
    for time in range(9, 17):
        for duration in range(30, 180, 30):
            start_time = time
            end_time = start_time + duration

            # Check if meeting time conflicts with anyone's schedule
            if (start_time not in artur_day_schedule or end_time <= artur_day_schedule[start_time][0]) and \
               (start_time not in michael_day_schedule or end_time <= michael_day_schedule[start_time][0]):
                # Check if meeting time is before Arthur's first meeting
                if artur_day_schedule and start_time < list(artur_day_schedule.keys())[0] or \
                   (not artur_day_schedule or artur_schedule.get(list(artur_day_schedule.keys())[0], (0, 0))[1] <= start_time):
                    # Check if meeting time is before Michael's first meeting
                    if michael_day_schedule and start_time < list(michael_day_schedule.keys())[0] or \
                       (not michael_day_schedule or michael_schedule.get(list(michael_day_schedule.keys())[0], (0, 0))[1] <= start_time):
                        # Check if meeting time is after everyone's last meeting
                        if end_time >= list(artur_day_schedule.keys())[-1] or artur_schedule.get(list(artur_day_schedule.keys())[-1], (0, 0))[0] >= end_time:
                            if end_time >= list(michael_day_schedule.keys())[-1] or michael_schedule.get(list(michael_day_schedule.keys())[-1], (0, 0))[0] >= end_time:
                                # Meeting time found
                                meeting_time = (day, f"{start_time:02d}:{60-start_time%60:02d}", f"{end_time:02d}:{60-end_time%60:02d}")
                                return meeting_time

    # If no meeting time is found, return None
    return None


# Define schedules
artur_schedule = {
    "Monday": [(11, 30), (13, 30), (15, 30)],
    "Tuesday": [(13, 30), (16, 30)],
    "Wednesday": [(10, 30), (11, 30), (12, 30), (14, 30), (16, 30)]
}

michael_schedule = {
    "Monday": [(9, 0), (12, 0), (14, 30), (15, 0)],
    "Tuesday": [(9, 30), (12, 30), (14, 30)],
    "Wednesday": [(10, 0), (13, 30)]
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