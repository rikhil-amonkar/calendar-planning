# Define the possible days and times
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
start_times = [(hour, minute) for hour in range(9, 17) for minute in [0, 30]]
end_times = [(hour, minute) for hour in range(9, 18) for minute in [0, 30]]

# Betty's schedule
betty_unavailable = [
    (10, 0), (10, 30),  # 10:00 to 10:30
    (11, 30), (12, 0), (12, 30),  # 11:30 to 12:30
    (16, 0), (16, 30),  # 16:00 to 16:30
    (9, 30), (10, 0),  # 9:30 to 10:00
    (10, 30), (11, 0),  # 10:30 to 11:00
    (12, 0), (12, 30),  # 12:00 to 12:30
    (13, 30), (14, 0), (14, 30),  # 13:30 to 15:00
    (16, 30), (17, 0),  # 16:30 to 17:00
    (13, 30), (14, 0),  # 13:30 to 14:00
    (14, 30), (15, 0),  # 14:30 to 15:00
    (9, 0), (10, 0),  # 9:00 to 10:00
    (11, 30), (12, 0),  # 11:30 to 12:00
    (12, 30), (13, 0),  # 12:30 to 13:00
    (14, 30), (15, 0),  # 14:30 to 15:00
]

# Megan's schedule
megan_unavailable = [
    (9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30), (17, 0),  # 9:00 to 17:00
    (9, 0), (9, 30),  # 9:00 to 9:30
    (10, 0), (10, 30),  # 10:00 to 10:30
    (12, 0), (12, 30), (13, 0), (13, 30),  # 12:00 to 14:00
    (15, 0), (15, 30),  # 15:00 to 15:30
    (16, 0), (16, 30),  # 16:00 to 16:30
    (9, 30), (10, 0),  # 9:30 to 10:30
    (11, 0), (11, 30),  # 11:00 to 11:30
    (12, 30), (13, 0),  # 12:30 to 13:00
    (13, 30), (14, 0),  # 13:30 to 14:30
    (15, 30), (16, 0), (16, 30), (17, 0),  # 15:30 to 17:00
    (9, 0), (9, 30),  # 9:00 to 10:30
    (11, 30), (12, 0), (12, 30), (13, 0),  # 11:30 to 14:00
    (14, 30), (15, 0),  # 14:30 to 15:00
    (15, 30), (16, 0),  # 15:30 to 16:30
    (9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30), (17, 0),  # 9:00 to 17:00
]

# Convert unavailable times to a set for quick lookup
betty_unavailable_set = set(betty_unavailable)
megan_unavailable_set = set(megan_unavailable)

# Function to check if a time slot is available
def is_available(day, start_time, end_time):
    if day == "Wednesday" or day == "Thursday":
        return False
    for hour in range(start_time[0], end_time[0] + 1):
        for minute in [0, 30]:
            if (hour, minute) in betty_unavailable_set or (hour, minute) in megan_unavailable_set:
                return False
    return True

# Find a valid meeting time
for day in days:
    for start_time in start_times:
        end_time = (start_time[0] + 1, start_time[1]) if start_time[1] == 0 else (start_time[0], start_time[1] + 30)
        if is_available(day, start_time, end_time):
            start_hour, start_minute = start_time
            end_hour, end_minute = end_time
            print(f"SOLUTION:\nDay: {day}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
            break
    else:
        continue
    break
else:
    print("No solution found")