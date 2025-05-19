from datetime import datetime, timedelta

# Define the working day details
day_of_week = "Monday"
work_start = datetime.strptime("09:00", "%H:%M")
work_end   = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define busy time intervals for each participant as (start, end) tuples
# All times are represented as datetime objects relative to the same arbitrary date.
# For simplicity, we use the same date for all events.
def to_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

juan_busy = [
    (to_time("09:00"), to_time("10:30")),
    (to_time("15:30"), to_time("16:00"))
]

marilyn_busy = [
    (to_time("11:00"), to_time("11:30")),
    (to_time("12:30"), to_time("13:00"))
]

ronald_busy = [
    (to_time("09:00"), to_time("10:30")),
    (to_time("12:00"), to_time("12:30")),
    (to_time("13:00"), to_time("13:30")),
    (to_time("14:00"), to_time("16:30"))
]

# Additional constraint: Juan cannot meet after 16:00, so adjust work_end for Juan.
juan_latest_end = to_time("16:00")

# Merge all busy intervals into one list for easier checking (they have to be checked separately)
all_busy = {
    "Juan": juan_busy,
    "Marilyn": marilyn_busy,
    "Ronald": ronald_busy
}

# Function to check if a proposed time slot [start, end) is free for a given person's schedule
def is_free(slot_start, slot_end, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # If the time slot overlaps with a busy interval, return False
        if slot_start < busy_end and busy_start < slot_end:
            return False
    return True

# Try to find a slot starting at work_start and moving in 15 minute increments.
# The meeting must finish by work_end and satisfy Juan's cutoff constraint.
current_start = work_start
found_slot = False
proposed_start = None

while current_start + meeting_duration <= work_end:
    proposed_end = current_start + meeting_duration
    # Respect Juan's limitation: meeting must end by 16:00
    if proposed_end > juan_latest_end:
        break
    
    # Check if all participants are free in this slot
    if (is_free(current_start, proposed_end, all_busy["Juan"]) and
        is_free(current_start, proposed_end, all_busy["Marilyn"]) and
        is_free(current_start, proposed_end, all_busy["Ronald"])):
        proposed_start = current_start
        found_slot = True
        break
    
    current_start += timedelta(minutes=15)

if found_slot:
    proposed_end = proposed_start + meeting_duration
    # Format the output in HH:MM:HH:MM format along with day of week.
    schedule_time = f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}"
    print(f"{day_of_week} {schedule_time}")
else:
    print("No suitable time slot found.")