# Define the work hours
start_work = (9, 30)
end_work = (17, 0)

# Define the blocked times for each participant
james_blocked = [(11, 30), (14, 30)]
john_blocked = [(9, 30), (11, 30), (12, 30), (14, 30), (16, 30)]

# Convert blocked times to minutes since 00:00
def to_minutes(time):
    return time[0] * 60 + time[1]

james_blocked_mins = [to_minutes(t) for t in james_blocked]
john_blocked_mins = [to_minutes(t) for t in john_blocked]

# Find the earliest available time slot that fits the meeting duration
meeting_duration = 60
current_time = start_work
day_of_week = "Monday"

while True:
    # Convert current_time to minutes
    current_mins = current_time[0] * 60 + current_time[1]
    
    # Check if there's space for the meeting before the next blocked time
    next_available = current_mins + meeting_duration
    next_blocked = None
    
    for block in john_blocked_mins + james_blocked_mins:
        if block >= current_mins:
            if next_available < block:
                next_available = block - meeting_duration
                next_blocked = block
                break
        else:
            if next_available < block:
                next_available = block - meeting_duration
                next_blocked = block
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