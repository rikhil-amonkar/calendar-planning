# Define constants
start_work = 9 * 60  # 9:00 AM in minutes
end_work = 17 * 60   # 5:00 PM in minutes

# Define busy intervals for each participant
busy_jack = [
    (9*60 + 30, 10*60 + 30),  # 9:30-10:30
    (11*60, 11*60 + 30),      # 11:00-11:30
    (12*60 + 30, 13*60),      # 12:30-13:00
    (14*60, 14*60 + 30),      # 14:00-14:30
    (16*60, 16*60 + 30),      # 16:00-16:30
]

busy_charlotte = [
    (9*60 + 30, 10*60),        # 9:30-10:00
    (10*60 + 30, 12*60),       # 10:30-12:00
    (12*60 + 30, 13*60 + 30),  # 12:30-13:30
    (14*60, 16*60),            # 14:00-16:00
]

# Function to compute available intervals
def get_available_intervals(busy_intervals, start_work, end_work):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    available = []
    prev_end = start_work
    for start, end in sorted_busy:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_work:
        available.append((prev_end, end_work))
    return available

# Compute available intervals for Jack and Charlotte
jack_available = get_available_intervals(busy_jack, start_work, end_work)
charlotte_available = get_available_intervals(busy_charlotte, start_work, end_work)

# Apply Jack's constraint: meeting must end by 12:30 (750 minutes)
jack_available_filtered = [ (s, e) for s, e in jack_available if e <= 750 ]

# Find overlapping intervals between Jack's filtered and Charlotte's available
candidates = []
for j_start, j_end in jack_available_filtered:
    for c_start, c_end in charlotte_available:
        overlap_start = max(j_start, c_start)
        overlap_end = min(j_end, c_end)
        if overlap_end - overlap_start >= 30:  # 30 minutes
            candidates.append( (overlap_start, overlap_end) )

# Find the earliest candidate
if candidates:
    earliest = min(candidates, key=lambda x: x[0])
    start_time = earliest[0]
    end_time = earliest[1]
    # Convert to time strings
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    start_str = minutes_to_time(start_time)
    end_str = minutes_to_time(end_time)
    day = "Monday"
    print(f"{start_str}:{end_str} {day}")
else:
    print("No suitable time found")