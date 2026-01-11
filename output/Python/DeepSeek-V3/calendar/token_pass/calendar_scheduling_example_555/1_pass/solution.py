def schedule_meeting(work_start, work_end, duration, preferences):
    """
    work_start, work_end: strings "HH:MM"
    duration: minutes
    preferences: dict with person: list of (block_start, block_end) and special constraints
    """
    # Convert time string to minutes since midnight
    def to_minutes(t):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    
    # Convert minutes back to HH:MM
    def to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"
    
    start_min = to_minutes(work_start)
    end_min = to_minutes(work_end)
    
    # Evelyn's constraint: not after 13:00 means meeting must end by 13:00
    evelyn_end_limit = to_minutes("13:00")
    
    # Randy's blocked times in minutes
    randy_blocks = [
        ("9:00", "10:30"),
        ("11:00", "15:30"),
        ("16:00", "17:00")
    ]
    randy_blocks_min = [(to_minutes(s), to_minutes(e)) for s, e in randy_blocks]
    
    # Generate free slots for Randy within work hours
    free_slots = []
    current = start_min
    for block_start, block_end in sorted(randy_blocks_min):
        if current < block_start:
            free_slots.append((current, block_start))
        current = max(current, block_end)
    if current < end_min:
        free_slots.append((current, end_min))
    
    # Filter slots that are at least `duration` long and end by Evelyn's limit
    possible_slots = []
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration:
            # Meeting must end by evelyn_end_limit
            meeting_end = slot_start + duration
            if meeting_end <= evelyn_end_limit:
                possible_slots.append((slot_start, meeting_end))
    
    if possible_slots:
        # Pick the earliest slot
        chosen_start, chosen_end = possible_slots[0]
        return "Monday", to_time(chosen_start), to_time(chosen_end)
    else:
        return None

# Given data
work_start = "9:00"
work_end = "17:00"
duration = 30
preferences = {}  # not used in this simple version, but kept for structure

result = schedule_meeting(work_start, work_end, duration, preferences)
if result:
    day, start, end = result
    print(f"{day}:{start}:{end}")
else:
    print("No suitable slot found")