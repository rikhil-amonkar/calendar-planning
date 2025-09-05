from datetime import timedelta, datetime

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define working day details (in minutes from midnight)
working_start = 9 * 60      # 9:00 -> 540
working_end   = 17 * 60     # 17:00 -> 1020
meeting_duration = 30       # duration in minutes

# Christine's meetings on Monday (start, end) in minutes
christine_meetings = [
    (11 * 60, 11 * 60 + 30),   # 11:00 to 11:30  -> (660, 690)
    (15 * 60, 15 * 60 + 30)    # 15:00 to 15:30  -> (900, 930)
]

# Helen's meetings on Monday (start, end) in minutes
helen_meetings = [
    (9 * 60 + 30, 10 * 60 + 30),   # 9:30 to 10:30   -> (570, 630)
    (11 * 60, 11 * 60 + 30),        # 11:00 to 11:30  -> (660, 690)
    (12 * 60, 12 * 60 + 30),        # 12:00 to 12:30  -> (720, 750)
    (13 * 60 + 30, 16 * 60),        # 13:30 to 16:00  -> (810, 960)
    (16 * 60 + 30, 17 * 60)         # 16:30 to 17:00  -> (990, 1020)
]

# Helen's additional constraint: she cannot meet after 15:00.
# Therefore, the meeting must end by or at 15:00 (15*60 = 900 minutes).
helen_latest_end = 15 * 60  # 15:00 in minutes

def is_slot_free(slot_start, slot_end, meetings):
    """
    Check if the given slot (slot_start, slot_end) does not conflict with any meeting in meetings.
    """
    for meeting_start, meeting_end in meetings:
        # If the slot overlaps with a meeting, return False
        if slot_start < meeting_end and slot_end > meeting_start:
            return False
    return True

# Find the first available slot that works for both Christine and Helen.
# We search from the start of the working day until the latest possible start for Helen.
latest_possible_start = min(working_end - meeting_duration, helen_latest_end - meeting_duration)

meeting_time = None

for candidate_start in range(working_start, latest_possible_start + 1):
    candidate_end = candidate_start + meeting_duration
    
    # Ensure Helen's meeting doesn't pass her limit of 15:00.
    if candidate_end > helen_latest_end:
        continue
    
    # Check if slot is within overall working hours (redundant for Christine here)
    if candidate_end > working_end:
        continue
    
    # Check availability for both Christine and Helen
    if is_slot_free(candidate_start, candidate_end, christine_meetings) and \
       is_slot_free(candidate_start, candidate_end, helen_meetings):
        meeting_time = (candidate_start, candidate_end)
        break

if meeting_time:
    start_str = minutes_to_time_str(meeting_time[0])
    end_str = minutes_to_time_str(meeting_time[1])
    # Output in the format "HH:MM:HH:MM" along with the day (Monday)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No available meeting slot found for the given constraints.")