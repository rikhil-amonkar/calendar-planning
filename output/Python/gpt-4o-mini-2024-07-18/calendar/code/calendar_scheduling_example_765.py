from datetime import datetime, timedelta

# Define participants' schedules
schedules = {
    "Joshua": {
        "Monday": [(15, 0, 15, 30)],
        "Tuesday": [(11, 30, 12, 0), (13, 0, 13, 30), (14, 30, 15, 0)],
        "Wednesday": []
    },
    "Joyce": {
        "Monday": [(9, 0, 9, 30), (10, 0, 11, 0), (11, 30, 12, 30), 
                   (13, 0, 15, 0), (15, 30, 17, 0)],
        "Tuesday": [(9, 0, 17, 0)],
        "Wednesday": [(9, 0, 9, 30), (10, 0, 11, 0), (12, 30, 15, 30), 
                      (16, 0, 16, 30)]
    }
}

# Meeting duration in minutes
meeting_duration = 30

# Convert schedule times to a list of unavailable time ranges
def create_unavailable_times(schedule):
    unavailable_times = []
    for times in schedule.values():
        for start_h, start_m, end_h, end_m in times:
            start = datetime(2023, 1, 1, start_h, start_m)
            end = datetime(2023, 1, 1, end_h, end_m)
            unavailable_times.append((start, end))
    return unavailable_times

# Check for available time slots
def find_available_time(day):
    start_time = datetime(2023, 1, 1, 9, 0)  # Work starts at 9:00
    end_time = datetime(2023, 1, 1, 17, 0)    # Work ends at 17:00

    # Get unavailable times for both participants
    joshua_unavailable = create_unavailable_times({day: schedules["Joshua"].get(day, [])})
    joyce_unavailable = create_unavailable_times({day: schedules["Joyce"].get(day, [])})

    # Merge unavailable times
    all_unavailable = sorted(joshua_unavailable + joyce_unavailable)

    # Check for gaps in unavailable times
    last_end = start_time
    for start, end in all_unavailable:
        if last_end + timedelta(minutes=meeting_duration) <= start:
            return last_end.strftime("%H:%M"), (last_end + timedelta(minutes=meeting_duration)).strftime("%H:%M")
        last_end = max(last_end, end)

    # Check after the last unavailable time
    if last_end + timedelta(minutes=meeting_duration) <= end_time:
        return last_end.strftime("%H:%M"), (last_end + timedelta(minutes=meeting_duration)).strftime("%H:%M")

    return None

# Attempt to find a time on preferred days
preferred_days = ["Tuesday", "Wednesday"]

for preferred_day in preferred_days:
    available_time = find_available_time(preferred_day)
    if available_time:
        start_time, end_time = available_time
        print(f"{start_time}:{end_time}, {preferred_day}")
        break