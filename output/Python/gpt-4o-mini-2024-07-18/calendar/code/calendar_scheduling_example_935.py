# Define participants' schedules
terry_schedule = {
    "Monday": [(10, 30), (12, 30), (15, 0)],
    "Tuesday": [(9, 30), (10, 30), (14, 0), (16, 0)],
    "Wednesday": [(9, 30), (11, 0), (13, 0), (15, 0), (16, 30)],
    "Thursday": [(9, 30), (12, 0), (13, 0), (16, 0)],
    "Friday": [(9, 0), (12, 0), (13, 30), (16, 30)],
}

frances_schedule = {
    "Monday": [(9, 30), (11, 0), (14, 0), (15, 0)],
    "Tuesday": [(9, 0), (10, 0), (11, 0), (13, 0), (15, 30)],
    "Wednesday": [(9, 30), (10, 30), (11, 30), (16, 30)],
    "Thursday": [(11, 0), (14, 30)],
    "Friday": [(9, 30), (11, 0), (13, 0), (16, 30)],
}

# Convert booked times to a more usable format
def convert_schedule(schedule):
    available_times = []
    for day, busy_slots in schedule.items():
        available_times.append((day, get_available_times(busy_slots)))
    return available_times

# Find available time slots based on busy schedule
def get_available_times(busy_slots):
    busy_slots = sorted(busy_slots)
    available_times = []
    day_start = (9, 0)  # work hours start
    day_end = (17, 0)   # work hours end
    
    last_end = day_start
    for start, end in busy_slots:
        if last_end < (start, 0):
            available_times.append((last_end, (start, 0)))
        last_end = (end, 0)
    
    if last_end < day_end:
        available_times.append((last_end, day_end))
    
    return available_times

# Combine available times for meeting
def find_meeting_time(terry_times, frances_times):
    potential_days = set(terry_times.keys()).intersection(frances_times.keys())
    
    for day in potential_days:
        terry_slots = terry_times[day]
        frances_slots = frances_times[day]
        
        for terry_start, terry_end in terry_slots:
            for frances_start, frances_end in frances_slots:
                start_time = max((terry_start, 0), (frances_start, 0))
                end_time = min((terry_end, 0), (frances_end, 0))
                
                if (end_time[0] - start_time[0] >= 0 and (end_time[1] - start_time[1]) >= 30):
                    return f"{day} {start_time[0]:02}:{start_time[1]:02}:{start_time[0]:02}:{start_time[1] + 30:02}"

# Calculate availability
terry_availability = convert_schedule(terry_schedule)
frances_availability = convert_schedule(frances_schedule)

# Find the meeting time
meeting_time = find_meeting_time(dict(terry_availability), dict(frances_availability))
print(meeting_time)