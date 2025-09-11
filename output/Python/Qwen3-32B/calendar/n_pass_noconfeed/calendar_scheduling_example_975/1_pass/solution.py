def to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def is_slot_free(schedule, day, start, duration=60):
    end = start + duration
    for b_start, b_end in schedule.get(day, []):
        if not (end <= b_start or start >= b_end):
            return False
    return True

nicole = {
    'Monday': [],
    'Tuesday': [(16*60, 16*60 + 30)],
    'Wednesday': [(15*60, 15*60 + 30)],
    'Thursday': [],
    'Friday': [
        (12*60, 12*60 + 30),
        (15*60 + 30, 16*60),
    ],
}

daniel = {
    'Monday': [
        (9*60, 12*60 + 30),
        (13*60, 13*60 + 30),
        (14*60, 16*60 + 30),
    ],
    'Tuesday': [
        (9*60, 10*60 + 30),
        (11*60 + 30, 12*60 + 30),
        (13*60, 13*60 + 30),
        (15*60, 16*60),
        (16*60 + 30, 17*60),
    ],
    'Wednesday': [
        (9*60, 10*60),
        (11*60, 12*60 + 30),
        (13*60, 13*60 + 30),
        (14*60, 14*60 + 30),
        (16*60 + 30, 17*60),
    ],
    'Thursday': [
        (11*60, 12*60),
        (13*60, 14*60),
        (15*60, 15*60 + 30),
    ],
    'Friday': [
        (10*60, 11*60),
        (11*60 + 30, 12*60),
        (12*60 + 30, 14*60 + 30),
        (15*60, 15*60 + 30),
        (16*60, 16*60 + 30),
    ],
}

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

for day in days:
    for start in range(540, 960 + 1):
        if is_slot_free(nicole, day, start, 60) and is_slot_free(daniel, day, start, 60):
            start_str = to_time(start)
            end_str = to_time(start + 60)
            print(f"{start_str}:{end_str} {day}")
            exit()