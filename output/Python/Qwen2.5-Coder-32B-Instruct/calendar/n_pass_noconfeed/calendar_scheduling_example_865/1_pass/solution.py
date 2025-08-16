from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = 9
work_end = 17
meeting_duration = 1

# Define the schedules for Megan and Daniel
megan_schedule = {
    'Monday': [(13, 13.5), (14, 15.5)],
    'Tuesday': [(9, 9.5), (12, 12.5), (16, 17)],
    'Wednesday': [(9.5, 10), (10.5, 11.5), (12.5, 14), (16, 16.5)],
    'Thursday': [(13.5, 14.5), (15, 15.5)]
}

daniel_schedule = {
    'Monday': [(10, 11.5), (12.5, 15)],
    'Tuesday': [(9, 10), (10.5, 17)],
    'Wednesday': [(9, 10), (10.5, 11.5), (12, 17)],
    'Thursday': [(9, 12), (12.5, 14.5), (15, 15.5), (16, 17)]
}

def find_free_slot(schedules, work_start, work_end, meeting_duration):
    days_of_week = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    for day in days_of_week:
        # Create a list of free slots for the current day
        free_slots = []
        current_time = work_start
        
        # Add initial free slot before the first meeting
        if schedules[day]:
            free_slots.append((current_time, schedules[day][0][0]))
        
        # Add free slots between meetings
        for i in range(len(schedules[day]) - 1):
            free_slots.append((schedules[day][i][1], schedules[day][i + 1][0]))
        
        # Add final free slot after the last meeting
        if schedules[day]:
            free_slots.append((schedules[day][-1][1], work_end))
        else:
            free_slots.append((current_time, work_end))
        
        # Check for a free slot that fits the meeting duration
        for start, end in free_slots:
            if end - start >= meeting_duration:
                return f"{start:.2f}:{end:.2f}", day
    
    return None, None

# Find a suitable time slot
time_slot, day = find_free_slot({**megan_schedule, **daniel_schedule}, work_start, work_end, meeting_duration)

# Output the result in the desired format
if time_slot:
    start_time, end_time = time_slot.split(':')
    print(f"{int(float(start_time))}:{int(float(start_time) % 1 * 60):02}:{int(float(end_time))}:{int(float(end_time) % 1 * 60):02} {day}")
else:
    print("No available time slot found.")