# Define the time slots in minutes from 00:00
time_slots = [(i, i + 60) for i in range(540, 1020, 60)]

# Define the unavailable periods for each participant
olivia_unavailable = [(750, 810), (870, 930), (990, 1020)]
anna_unavailable = []
virginia_unavailable = [(600, 660), (750, 960), (990, 1020)]
paul_unavailable = [(570, 570), (690, 720), (780, 840), (870, 930), (990, 1020)]

# Function to check if a time slot is available for all participants
def is_slot_available(slot):
    start, end = slot
    for unavailable in olivia_unavailable + anna_unavailable + virginia_unavailable + paul_unavailable:
        if not (end <= unavailable[0] or start >= unavailable[1]):
            return False
    return True

# Find a valid time slot
valid_slot = None
for slot in time_slots:
    if is_slot_available(slot):
        valid_slot = slot
        break

# Print the valid slot if found
if valid_slot:
    start_time_minutes, end_time_minutes = valid_slot
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")