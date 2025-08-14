def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define busy times for each participant in minutes since midnight
patrick = [(9*60 + 0, 9*60 + 30), (10*60 + 0, 10*60 + 30), (13*60 + 30, 14*60 + 0), (16*60 + 0, 16*60 + 30)]
kayla = [(12*60 + 30, 13*60 + 30), (15*60 + 0, 15*60 + 30), (16*60 + 0, 16*60 + 30)]
carl = [(10*60 + 30, 11*60 + 0), (12*60 + 0, 12*60 + 30), (13*60 + 0, 13*60 + 30), (14*60 + 30, 17*60 + 0)]
christian = [(9*60 + 0, 12*60 + 30), (13*60 + 0, 14*60 + 0), (14*60 + 30, 17*60 + 0)]

# All participants' busy times
participants = [patrick, kayla, carl, christian]

# Generate all possible 30-minute slots between 9:00 and 17:00
start_work = 9 * 60
end_work = 17 * 60
duration = 30

for start in range(start_work, end_work, 30):
    end = start + 30
    # Check if this slot is free for all
    valid = True
    for busy_times in participants:
        for (b_start, b_end) in busy_times:
            # Check overlap: [start, end) and [b_start, b_end)
            if start < b_end and b_start < end:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"{start_time}:{end_time} Monday")
        break