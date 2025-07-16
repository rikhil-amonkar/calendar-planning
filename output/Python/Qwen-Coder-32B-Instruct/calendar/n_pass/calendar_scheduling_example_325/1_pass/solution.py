from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define the constraints for each participant
constraints = {
    "Jose": [datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M"),
             datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M"),
             datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")],  # Jose doesn't want to meet after 15:30
    "Keith": [datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"),
              datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")],
    "Logan": [datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M"),
              datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"),
              datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")],
    "Megan": [datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M"),
              datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M"),
              datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"),
              datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M")],
    "Gary": [datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M"),
             datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M"),
             datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M"),
             datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M"),
             datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M")],
    "Bobby": [datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M"),
              datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"),
              datetime.strptime("13:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")]
}

# Function to check if a time slot is available for all participants
def is_slot_available(slot_start, slot_end):
    for person, person_constraints in constraints.items():
        for i in range(0, len(person_constraints), 2):
            if slot_start < person_constraints[i+1] and slot_end > person_constraints[i]:
                return False
    return True

# Find a suitable time slot
current_time = work_start
while current_time + meeting_duration <= work_end:
    if is_slot_available(current_time, current_time + meeting_duration):
        meeting_start = current_time.strftime("%H:%M")
        meeting_end = (current_time + meeting_duration).strftime("%H:%M")
        print(f"{meeting_start}:{meeting_end} Monday")
        break
    current_time += timedelta(minutes=30)