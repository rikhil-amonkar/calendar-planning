# Define the working hours
start_time = '09:00'
end_time = '17:00'

# Patrick's busy periods (start:end)
busy_periods = [
    '09:00-09:30',
    '10:30-12:00',
    '12:30-13:30',
    '14:00-14:30',
    '15:00-16:30'
]

# Convert busy periods to time objects
busy = []
for period in busy_periods:
    start, end = period.split('-')
    start_h = int(start[0:2])
    end_h = int(end[0:2])
    busy.append((start_h, end_h))

# Convert start and end times to minutes since 09:00
def to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

start = to_minutes(start_time)
end = to_minutes(end_time)

# Patrick's busy times in minutes
pat_busy = []
for b in busy:
    pat_busy.append((b[0], b[1]))

# Find available slots for Patrick
available = []
for t in range(start, end):
    available.append(t)

# Check each available time against Patrick's busy periods
for time in available:
    is_available = True
    for b in pat_busy:
        if b[0] <= time <= b[1]:
            is_available = False
            break
    if is_available:
        print(f"{time:02d}:{time//60:02d} to {time + 30:02d}:{(time + 30)//60:02d}")
        break
