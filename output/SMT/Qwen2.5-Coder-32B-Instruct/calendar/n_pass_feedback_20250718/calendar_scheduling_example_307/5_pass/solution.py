# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the participants
participants = ['Ronald', 'Stephen', 'Brittany', 'Dorothy', 'Rebecca', 'Jordan']

# Define the blocked time slots for each participant
blocked_slots = {
    'Ronald': [],
    'Stephen': [1000, 1030, 1200, 1230],
    'Brittany': [1100, 1130, 1330, 1400, 1530, 1600, 1630],
    'Dorothy': [900, 930, 1000, 1030, 1100, 1200, 1230, 1300, 1330, 1400, 1500, 1530, 1600],
    'Rebecca': [930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600],
    'Jordan': [900, 930, 1000, 1030, 1100, 1130, 1200, 1300, 1330, 1400, 1430, 1500, 1530, 1600]
}

# Define the meeting duration (30 minutes)
meeting_duration = 30

# Function to check if a time slot is available for all participants
def is_time_slot_available(start_time):
    for participant in participants:
        for blocked_time in blocked_slots[participant]:
            if start_time == blocked_time or start_time + meeting_duration == blocked_time:
                return False
    return True

# Iterate through each time slot to find a valid meeting time
for start_time in time_slots:
    if is_time_slot_available(start_time):
        end_time = start_time + meeting_duration
        start_time_str = f"{start_time // 100:02}:{start_time % 100:02}"
        end_time_str = f"{end_time // 100:02}:{end_time % 100:02}"
        print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
        break
else:
    print("No solution found")