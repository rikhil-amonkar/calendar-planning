def time_to_minutes(t):
    """Convert HH:MM to minutes from 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to HH:MM."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def find_meeting_slot(jack_busy, charlotte_busy, work_start, work_end, duration, preference_cutoff):
    """
    jack_busy: list of (start, end) in minutes from 00:00
    charlotte_busy: same
    work_start, work_end: minutes from 00:00
    duration: minutes
    preference_cutoff: minutes from 00:00, prefer slots starting before this time.
    """
    # Generate free slots for Jack
    jack_free = []
    current = work_start
    for start, end in sorted(jack_busy):
        if start > current:
            jack_free.append((current, start))
        current = max(current, end)
    if current < work_end:
        jack_free.append((current, work_end))
    
    # Generate free slots for Charlotte
    charlotte_free = []
    current = work_start
    for start, end in sorted(charlotte_busy):
        if start > current:
            charlotte_free.append((current, start))
        current = max(current, end)
    if current < work_end:
        charlotte_free.append((current, work_end))
    
    # Find intersection of free slots with enough duration
    possible_slots = []
    for js, je in jack_free:
        for cs, ce in charlotte_free:
            s = max(js, cs)
            e = min(je, ce)
            if e - s >= duration:
                possible_slots.append((s, e))
    
    # Sort by start time
    possible_slots.sort(key=lambda x: x[0])
    
    # Prefer slots starting before preference_cutoff
    preferred = [slot for slot in possible_slots if slot[0] < preference_cutoff]
    if preferred:
        chosen = preferred[0]
    elif possible_slots:
        chosen = possible_slots[0]
    else:
        return None
    
    meeting_start = chosen[0]
    meeting_end = meeting_start + duration
    return meeting_start, meeting_end

def main():
    # Work hours 9:00 to 17:00
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    
    # Jack's busy times (Monday)
    jack_busy = [
        ("9:30", "10:30"),
        ("11:00", "11:30"),
        ("12:30", "13:00"),
        ("14:00", "14:30"),
        ("16:00", "16:30")
    ]
    jack_busy = [(time_to_minutes(s), time_to_minutes(e)) for s, e in jack_busy]
    
    # Charlotte's busy times (Monday)
    charlotte_busy = [
        ("9:30", "10:00"),
        ("10:30", "12:00"),
        ("12:30", "13:30"),
        ("14:00", "16:00")
    ]
    charlotte_busy = [(time_to_minutes(s), time_to_minutes(e)) for s, e in charlotte_busy]
    
    duration = 30  # minutes
    preference_cutoff = time_to_minutes("12:30")  # Jack prefers before 12:30
    
    result = find_meeting_slot(jack_busy, charlotte_busy, work_start, work_end, duration, preference_cutoff)
    
    if result:
        start_min, end_min = result
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        print(f"Monday {{{start_time}:{end_time}}}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()