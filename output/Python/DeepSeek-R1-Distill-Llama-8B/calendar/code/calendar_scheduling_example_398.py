# Define the work hours
start_work = (9, 0)
end_work = (17, 0)

# Define the blocked times for each participant
doris_blocked = [(9, 0), (10, 0), (13, 30), (16, 0), (16, 30)]
theresa_blocked = [(10, 0), (12, 0)]
christian_blocked = []
terry_blocked = [(9, 30), (11, 30), (12, 30), (13, 30), (14, 30), (15, 30), (16, 30)]
carolyn_blocked = [(9, 0), (10, 30), (11, 0), (12, 0), (13, 30), (15, 0), (16, 0), (17, 0)]
kyle_blocked = [(9, 0), (11, 30), (12, 30), (14, 30)]

# Convert blocked times to minutes since 00:00
def to_minutes(time):
    return time[0] * 60 + time[1]

doris_blocked_mins = [to_minutes(t) for t in doris_blocked]
theresa_blocked_mins = [to_minutes(t) for t in theresa_blocked]
christian_blocked_mins = [to_minutes(t) for t in christian_blocked]
terry_blocked_mins = [to_minutes(t) for t in terry_blocked]
carolyn_blocked_mins = [to_minutes(t) for t in carolyn_blocked]
kyle_blocked_mins = [to_minutes(t) for t in kyle_blocked]

# Combine all blocked times
all_blocked = [
    (0, 60),
    (60, 120),
    (90, 120),
    (120, 150),
    (150, 180),
    (180, 240),
    (210, 225),
    (240, 420)
]

# Sort the blocked intervals
all_blocked.sort()

# Find the earliest available time slot that fits the meeting duration
meeting_duration = 30
current_time = start_work
day_of_week = "Monday"

while True:
    # Convert current_time to minutes
    current_mins = current_time[0] * 60 + current_time[1]
    
    # Check if there's space for the meeting before the next blocked time
    next_available = current_mins + meeting_duration
    next_blocked = None
    
    for block in all_blocked:
        if block[0] >= current_mins:
            if next_available < block[0]:
                next_available = block[0] - meeting_duration
                next_blocked = block[0]
                break
        else:
            if next_available < block[1]:
                next_available = block[1] - meeting_duration
                next_blocked = block[1]
                break
    
    # If found a suitable slot, break the loop
    if next_blocked is not None:
        break
    
    # Move to the next hour if no slot is found
    if current_time[1] == 59:
        current_time = (current_time[0] + 1, 0)
    else:
        current_time = (current_time[0], current_time[1] + 1)

# Convert next_available back to hours and minutes
start_hh, start_mm = divmod(next_available, 60)
end_hh, end_mm = divmod(next_available + meeting_duration, 60)

# Format the output
print(f"{start_hh:02}:{start_mm:02}:{end_hh:02}:{end_mm:02}")
print(f"{day_of_week}")