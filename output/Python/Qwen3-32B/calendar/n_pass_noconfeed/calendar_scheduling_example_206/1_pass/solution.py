import datetime

def generate_free_intervals(business_intervals, work_start=540, work_end=1020):
    business = sorted(business_intervals, key=lambda x: x[0])
    free_intervals = []
    previous_end = work_start
    for start, end in business:
        if start > previous_end:
            free_intervals.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < work_end:
        free_intervals.append((previous_end, work_end))
    return free_intervals

# Participants' busy intervals
participants_busy = {
    'Shirley': [(630, 660), (720, 750)],
    'Jacob': [(540, 570), (600, 630), (660, 690), (750, 810), (870, 900)],
    'Stephen': [(690, 720), (750, 780)],
    'Margaret': [(540, 570), (630, 750), (780, 810), (900, 930), (990, 1020)],
    'Mason': [(540, 600), (630, 660), (690, 750), (780, 810), (840, 870), (990, 1020)]
}

# Generate free intervals for each participant
free_intervals = {}
for name, busy in participants_busy.items():
    free_intervals[name] = generate_free_intervals(busy)

# Process Margaret's constraint: start >= 870 (14:30)
margaret_name = 'Margaret'
margaret_free = free_intervals[margaret_name]
processed_margaret = []
for s, e in margaret_free:
    if e <= 870:
        continue
    if s < 870:
        if e > 870:
            processed_margaret.append((870, e))
    else:
        processed_margaret.append((s, e))
free_intervals[margaret_name] = processed_margaret

# Collect participant names
participant_names = list(participants_busy.keys())

# Initialize candidates with the first participant's free intervals
candidates = free_intervals[participant_names[0]]

# Process the remaining participants
for name in participant_names[1:]:
    current_free = free_intervals[name]
    new_candidates = []
    for candidate in candidates:
        c_start, c_end = candidate
        for free in current_free:
            f_start, f_end = free
            overlap_start = max(c_start, f_start)
            overlap_end = min(c_end, f_end)
            if overlap_end - overlap_start >= 30:
                new_candidates.append((overlap_start, overlap_end))
    # Deduplicate and sort
    new_candidates = sorted(set(new_candidates))
    candidates = new_candidates

# Find the earliest candidate and output
if candidates:
    earliest = min(candidates, key=lambda x: x[0])
    start_time = earliest[0]
    end_time = start_time + 30  # Meeting duration is 30 minutes
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    start_str = to_time_str(start_time)
    end_str = to_time_str(end_time)
    day = "Monday"
    print(f"{start_str}:{end_str} {day}")
else:
    print("No suitable time found")