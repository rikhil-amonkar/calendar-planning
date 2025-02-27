# Define work hours in minutes since 9:00 AM (work_start = 0, work_end = 480)
work_start = 0
work_end = 480
meeting_duration = 30

# Read Patrick's busy periods and convert to minutes since 9:00
busy = [
    (0, 30),
    (90, 180),
    (210, 270),
    (300, 330),
    (390, 510)
]

# Sort the busy periods (though they are already sorted)
busy.sort()

earliest = None

# Check for available slot before the first busy period
if busy[0][0] > 0:
    available = busy[0][0] - 0
    if available >= meeting_duration:
        earliest = 0 + meeting_duration

# Check for available slot between consecutive busy periods
for i in range(len(busy) - 1):
    end_prev = busy[i][1]
    start_next = busy[i+1][0]
    available = start_next - end_prev
    if available >= meeting_duration:
        earliest = end_prev + meeting_duration
        break

# Check for available slot after the last busy period
if not busy or busy[-1][1] < work_end:
    available = work_end - busy[-1][1]
    if available >= meeting_duration:
        earliest = busy[-1][1] + meeting_duration

# Convert the earliest time to a readable format
if earliest is not None:
    start_min = earliest
    end_min = earliest + meeting_duration
    hours = start_min // 60
    minutes = start_min % 60
    print(f"Monday, {hours:02d}:{minutes:02d} - {hours:02d}:{minutes:02d + 30}")
else:
    print("No available time slot found.")
