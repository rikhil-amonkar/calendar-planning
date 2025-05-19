from datetime import datetime, timedelta

# Define the participants' schedules
larry_schedule = [(9, 0, 17, 0)]  # Open entire week
samuel_schedule = {
    'Monday': [(10, 30, 11, 0), (12, 0, 12, 30), (13, 0, 15, 0), (15, 30, 16, 30)],
    'Tuesday': [(9, 0, 12, 0), (14, 0, 15, 30), (16, 30, 17, 0)],
    'Wednesday': [(10, 30, 11, 0), (11, 30, 12, 0), (12, 30, 13, 0), (14, 0, 14, 30), (15, 0, 16, 0)]
}

# Meeting constraints
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
preferred_days = ['Monday', 'Tuesday', 'Wednesday']
larry_avoids = ['Wednesday']
samuel_avoids = ['Tuesday']

def find_available_time(schedules):
    for day in preferred_days:
        # Skip if Larry wants to avoid this day
        if day in larry_avoids:
            continue

        # Get the working hours of the day
        work_hours = (work_start.hour, work_start.minute, work_end.hour, work_end.minute)
        free_slots = []

        # Generate free slots for the whole day
        current_time = work_start
        while current_time < work_end:
            slot_start = current_time
            slot_end = slot_start + meeting_duration
            
            # Check if the slot is available
            is_free = True
            # Check Samuel's schedule for the day
            for scheduled_start, scheduled_end in samuel_schedule[day]:
                scheduled_start_time = datetime.strptime(f"{scheduled_start}:00", "%H:%M:%S")
                scheduled_end_time = datetime.strptime(f"{scheduled_end}:00", "%H:%M:%S")
                if slot_start < scheduled_end_time and slot_end > scheduled_start_time:
                    is_free = False
                    break
            
            if is_free and slot_end <= work_end:
                free_slots.append((slot_start, slot_end))
            
            # Move to the next time slot
            current_time += timedelta(minutes=30)  # Check every 30 minutes

        # Find the earliest available slot
        if free_slots:
            earliest_slot = free_slots[0]
            return earliest_slot[0].strftime("%H:%M") + ":" + earliest_slot[1].strftime("%H:%M"), day 

# Calculate the proposed time
time_range, day_of_week = find_available_time(samuel_schedule)

print(f"{time_range} {day_of_week}")