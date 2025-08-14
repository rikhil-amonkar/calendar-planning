work_start = 9 * 60  # 540 minutes
work_end = 17 * 60   # 1020 minutes

# Define busy intervals for each participant
busy_intervals = {
    'Walter': [],
    'Cynthia': [
        (9*60, 9*60 + 30),  # 9:00-9:30
        (10*60, 10*60 + 30),  # 10:00-10:30
        (13*60 + 30, 14*60 + 30),  # 13:30-14:30
        (15*60, 16*60)  # 15:00-16:00
    ],
    'Ann': [
        (10*60, 11*60),  # 10:00-11:00
        (13*60, 13*60 + 30),  # 13:00-13:30
        (14*60, 15*60),  # 14:00-15:00
        (16*60, 16*60 + 30)  # 16:00-16:30
    ],
    'Catherine': [
        (9*60, 11*60 + 30),  # 9:00-11:30
        (12*60 + 30, 13*60 + 30),  # 12:30-13:30
        (14*60 + 30, 17*60)  # 14:30-17:00
    ],
    'Kyle': [
        (9*60, 9*60 + 30),  # 9:00-9:30
        (10*60, 11*60 + 30),  # 10:00-11:30
        (12*60, 12*60 + 30),  # 12:00-12:30
        (13*60, 14*60 + 30),  # 13:00-14:30
        (15*60, 16*60)  # 15:00-16:00
    ]
}

participants = ['Walter', 'Cynthia', 'Ann', 'Catherine', 'Kyle']

# Generate available arrays for each participant
available_arrays = []
for participant in participants:
    busy = busy_intervals[participant]
    length = work_end - work_start + 1
    available = [True] * length
    for start, end in busy:
        for m in range(start, end):
            offset = m - work_start
            if 0 <= offset < length:
                available[offset] = False
    available_arrays.append(available)

# Compute overall available array
overall_available = [all(arr[i] for arr in available_arrays) for i in range(len(available_arrays[0]))]

# Find the first 30-minute block
start_idx = -1
current_length = 0
for i in range(len(overall_available)):
    if overall_available[i]:
        current_length += 1
        if current_length == 30:
            start_idx = i - 29
            break
    else:
        current_length = 0

# Convert to time strings
def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

start_minute = work_start + start_idx
end_minute = start_minute + 30
start_time = to_time_str(start_minute)
end_time = to_time_str(end_minute)
day = "Monday"

print(f"{start_time}:{end_time} {day}")