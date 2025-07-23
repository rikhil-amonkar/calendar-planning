# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the participants and their blocked time slots
participants = {
    "Doris": [900, 930, 1000, 1030, 1330, 1400, 1600, 1630],
    "Theresa": [1000, 1030, 1100, 1130],
    "Christian": [],
    "Terry": [930, 1000, 1030, 1130, 1200, 1230, 1330, 1400, 1430, 1500, 1530, 1600, 1630],
    "Carolyn": [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1330, 1400, 1430, 1500, 1530, 1600, 1630],
    "Kyle": [900, 930, 1130, 1200, 1230, 1430, 1500, 1530, 1600, 1630]
}

# Function to check if a time slot is available for all participants
def is_available(time_slot, participants):
    for participant, blocked_slots in participants.items():
        if time_slot in blocked_slots or (time_slot + 30) in blocked_slots:
            return False
    return True

# Find the first available time slot
start_time = None
for t in time_slots:
    if is_available(t, participants):
        start_time = t
        end_time = t + 30
        break

# Check if a valid meeting time was found
if start_time is not None:
    # Format the output
    start_time_str = f"{start_time // 100:02}:{start_time % 100:02}"
    end_time_str = f"{end_time // 100:02}:{end_time % 100:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")