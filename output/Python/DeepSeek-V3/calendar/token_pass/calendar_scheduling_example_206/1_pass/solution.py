def time_to_min(t_str):
    # t_str format "HH:MM"
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Work hours
work_start = time_to_min("9:00")
work_end = time_to_min("17:00")
duration = 30

# Busy intervals in minutes from midnight? No, from 0 as 9:00.
# But easier: store as absolute minutes from 0:00, then subtract 9:00*60 later? 
# Let's do all in minutes from 9:00 = 0.
def convert_interval(start_str, end_str):
    s = time_to_min(start_str) - 540  # 9:00 = 540 min from midnight
    e = time_to_min(end_str) - 540
    return (s, e)

# Shirley
shirley_busy = [
    convert_interval("10:30", "11:00"),
    convert_interval("12:00", "12:30")
]

# Jacob
jacob_busy = [
    convert_interval("9:00", "9:30"),
    convert_interval("10:00", "10:30"),
    convert_interval("11:00", "11:30"),
    convert_interval("12:30", "13:30"),
    convert_interval("14:30", "15:00")
]

# Stephen
stephen_busy = [
    convert_interval("11:30", "12:00"),
    convert_interval("12:30", "13:00")
]

# Margaret
margaret_busy = [
    convert_interval("9:00", "9:30"),
    convert_interval("10:30", "12:30"),
    convert_interval("13:00", "13:30"),
    convert_interval("15:00", "15:30"),
    convert_interval("16:30", "17:00")
]

# Mason
mason_busy = [
    convert_interval("9:00", "10:00"),
    convert_interval("10:30", "11:00"),
    convert_interval("11:30", "12:30"),
    convert_interval("13:00", "13:30"),
    convert_interval("14:00", "14:30"),
    convert_interval("16:30", "17:00")
]

def is_free(person_busy, start, end):
    for bs, be in person_busy:
        if not (end <= bs or start >= be):
            return False
    return True

# Margaret's preference: not before 14:30
pref_start_min = time_to_min("14:30") - 540  # 330

# Search
found = None
for start in range(pref_start_min, work_end - work_start - duration + 1):
    end = start + duration
    if all([
        is_free(shirley_busy, start, end),
        is_free(jacob_busy, start, end),
        is_free(stephen_busy, start, end),
        is_free(margaret_busy, start, end),
        is_free(mason_busy, start, end)
    ]):
        found = (start, end)
        break

if found:
    start_abs = found[0] + 540  # back to minutes from midnight
    end_abs = found[1] + 540
    start_time = min_to_time(start_abs)
    end_time = min_to_time(end_abs)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No suitable time found")