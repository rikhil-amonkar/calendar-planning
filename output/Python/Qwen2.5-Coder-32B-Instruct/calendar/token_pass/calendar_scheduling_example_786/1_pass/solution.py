from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, days, start_time, end_time, preferences):
    # Convert start and end times to datetime objects for easier manipulation
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Create a list of time slots in 30-minute increments
    time_slots = []
    current_time = start
    while current_time < end:
        time_slots.append(current_time)
        current_time += timedelta(minutes=30)
    
    # Initialize availability dictionary for each participant
    availability = {participant: {day: [True] * len(time_slots) for day in days} for participant in participants}
    
    # Mark busy slots for each participant
    for participant, schedule in participants.items():
        for day, busy_times in schedule.items():
            for busy_start_str, busy_end_str in busy_times:
                busy_start = datetime.strptime(busy_start_str, "%H:%M")
                busy_end = datetime.strptime(busy_end_str, "%H:%M")
                
                # Find the indices of the busy time slots
                start_index = time_slots.index(busy_start)
                end_index = time_slots.index(busy_end)
                
                # Mark these slots as busy
                for i in range(start_index, end_index):
                    availability[participant][day][i] = False
    
    # Find common free slots
    common_free_slots = {}
    for day in days:
        common_free_slots[day] = []
        for i in range(len(time_slots) - meeting_duration + 1):
            if all(availability[participant][day][i] for participant in participants):
                # Check if this slot meets the preferences
                valid = True
                for participant, pref in preferences.items():
                    if pref.get(day) and time_slots[i] < datetime.strptime(pref[day], "%H:%M"):
                        valid = False
                        break
                if valid:
                    common_free_slots[day].append((time_slots[i], time_slots[i + meeting_duration]))
    
    # Select the first valid slot found
    for day, slots in common_free_slots.items():
        if slots:
            start_slot, end_slot = slots[0]
            return f"{start_slot.strftime('%H:%M')}:{end_slot.strftime('%H:%M')}", day

# Define participants' schedules and preferences
participants = {
    "Amy": {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [("11:00", "11:30"), ("13:30", "14:00")]
    },
    "Pamela": {
        "Monday": [("9:00", "10:30"), ("11:00", "16:30")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "17:00")],
        "Wednesday": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "13:30"), ("14:30", "15:00"), ("16:00", "16:30")]
    }
}

preferences = {
    "Pamela": {
        "Monday": "16:00",
        "Tuesday": "16:00",
        "Wednesday": "16:00"
    }
}

meeting_duration = 1  # 30 minutes
days = ["Monday", "Tuesday", "Wednesday"]
start_time = "09:00"
end_time = "17:00"

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time(participants, meeting_duration, days, start_time, end_time, preferences)
print(f"Meeting time: {meeting_time} on {meeting_day}")