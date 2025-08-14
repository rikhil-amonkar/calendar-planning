def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def is_time_free(busy_intervals, start, end):
    for bus_start, bus_end in busy_intervals:
        if bus_start < end and bus_end > start:
            return False
    return True

# Define the busy intervals for each person in minutes since midnight
julie_busy = [
    (9*60, 9*60 + 30),          # 9:00-9:30
    (11*60, 11*60 + 30),        # 11:00-11:30
    (12*60, 12*60 + 30),        # 12:00-12:30
    (13*60 + 30, 14*60),        # 13:30-14:00
    (16*60, 17*60)              # 16:00-17:00
]

sean_busy = [
    (9*60, 9*60 + 30),          # 9:00-9:30
    (13*60, 13*60 + 30),        # 13:00-13:30
    (15*60, 15*60 + 30),        # 15:00-15:30
    (16*60, 16*60 + 30)         # 16:00-16:30
]

lori_busy = [
    (10*60, 10*60 + 30),        # 10:00-10:30
    (11*60, 13*60),             # 11:00-13:00
    (15*60 + 30, 17*60)         # 15:30-17:00
]

# Work hours from 9:00 (540) to 17:00 (1020)
# Meeting duration is 60 minutes, so latest start is 16:00 (960)
day = "Monday"
found = False

for start in range(9*60, 16*60 + 1):  # 9:00 to 16:00 inclusive
    end = start + 60
    if is_time_free(julie_busy, start, end) and is_time_free(sean_busy, start, end) and is_time_free(lori_busy, start, end):
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"{start_time}:{end_time} {day}")
        found = True
        break

if not found:
    print("No suitable time found.")