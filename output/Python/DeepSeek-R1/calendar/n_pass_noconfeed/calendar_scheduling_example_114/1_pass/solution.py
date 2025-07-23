def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time_str(minutes):
    total_minutes = minutes
    h = 9 + total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Define participants' busy intervals
participants_busy = {
    "Stephanie": [("10:00", "10:30"), ("16:00", "16:30")],
    "Cheryl": [("10:00", "10:30"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:30", "17:00")],
    "Bradley": [("9:30", "10:00"), ("10:30", "11:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Steven": [("9:00", "12:00"), ("13:00", "13:30"), ("14:30", "17:00")]
}

# Initialize common_free array (480 minutes from 9:00 to 17:00)
common_free = [True] * 480  # 0 to 479

# Process each participant's busy intervals
for name, intervals in participants_busy.items():
    part_free = [True] * 480
    for start_str, end_str in intervals:
        s = time_str_to_minutes(start_str)
        e = time_str_to_minutes(end_str)
        end_index = min(e, 480)
        if s < 480:
            for i in range(s, end_index):
                if i < 480:
                    part_free[i] = False
    # Update common_free: only free if free in common and free for this participant
    for i in range(480):
        common_free[i] = common_free[i] and part_free[i]

# Find the first contiguous free block of 60 minutes
current_run = 0
start_index = -1
for i in range(480):
    if common_free[i]:
        current_run += 1
    else:
        current_run = 0
    if current_run >= 60:
        start_index = i - 59
        break

# Convert start index to time
start_minutes = start_index
end_minutes = start_index + 60
start_time = minutes_to_time_str(start_minutes)
end_time = minutes_to_time_str(end_minutes)

# Output the result
print("Monday")
print(f"{start_time}:{end_time}")