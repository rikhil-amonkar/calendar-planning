def intervals_overlap(s1, e1, s2, e2):
    return s1 < e2 and s2 < e1

# Define busy intervals in minutes since midnight
patrick_busy = [
    (9*60, 9*60 + 30),  # 9:00-9:30
    (10*60, 10*60 + 30),  # 10:00-10:30
    (13*60 + 30, 14*60),  # 13:30-14:00
    (16*60, 16*60 + 30)  # 16:00-16:30
]
kayla_busy = [
    (12*60 + 30, 13*60 + 30),  # 12:30-13:30
    (15*60, 15*60 + 30),  # 15:00-15:30
    (16*60, 16*60 + 30)  # 16:00-16:30
]
carl_blocked = [
    (10*60 + 30, 11*60),  # 10:30-11:00
    (12*60, 12*60 + 30),  # 12:00-12:30
    (13*60, 13*60 + 30),  # 13:00-13:30
    (14*60 + 30, 17*60)  # 14:30-17:00
]
christian_blocked = [
    (9*60, 12*60 + 30),  # 9:00-12:30
    (13*60, 14*60),  # 13:00-14:00
    (14*60 + 30, 17*60)  # 14:30-17:00
]

participants = [patrick_busy, kayla_busy, carl_blocked, christian_blocked]

# Iterate through possible start times
for start in range(540, 990 + 1):  # 9:00 to 16:30
    end = start + 30
    valid = True
    for busy_intervals in participants:
        for (bs, be) in busy_intervals:
            if intervals_overlap(start, end, bs, be):
                valid = False
                break
        if not valid:
            break
    if valid:
        # Convert to time strings
        def to_time(m):
            h = m // 60
            minute = m % 60
            return f"{h:02d}:{minute:02d}"
        start_time = to_time(start)
        end_time = to_time(end)
        print(f"{start_time}:{end_time} Monday")
        break