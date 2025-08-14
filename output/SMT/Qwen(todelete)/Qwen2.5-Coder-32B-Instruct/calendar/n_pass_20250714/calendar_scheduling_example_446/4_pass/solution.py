# Define the time slots from 9:00 to 17:00 in 30-minute intervals
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Define busy times for each participant
busy_times = {
    "Megan": [(9, 0), (9, 30), (10, 0), (10, 30), (12, 0), (12, 30)],
    "Christine": [(9, 0), (9, 30), (11, 30), (12, 0), (13, 0), (14, 0), (15, 30), (16, 0)],
    "Gabriel": [],
    "Sara": [(11, 30), (12, 0), (14, 30), (15, 0)],
    "Bruce": [(9, 30), (10, 0), (10, 30), (12, 0), (12, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0)],
    "Kathryn": [(h, m) for h in range(10, 15) for m in [0, 30]] + [(15, 0), (15, 30), (16, 0)],
    "Billy": [(9, 0), (9, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30)]
}

# Function to check if a time slot is available for all participants
def is_slot_available(start_slot, end_slot, busy_times):
    for participant, busy in busy_times.items():
        for busy_start in busy:
            busy_end = (busy_start[0] + 1, 0) if busy_start[1] == 30 else (busy_start[0], 30)
            if not (end_slot <= busy_start or start_slot >= busy_end):
                return False
    return True

# Find a valid 30-minute slot
for i in range(len(time_slots) - 1):
    start_slot = time_slots[i]
    end_slot = time_slots[i + 1]
    if is_slot_available(start_slot, end_slot, busy_times):
        start_hour, start_minute = start_slot
        end_hour, end_minute = end_slot
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02}:{start_minute:02}")
        print(f"End Time: {end_hour:02}:{end_minute:02}")
        break
else:
    print("No solution found")