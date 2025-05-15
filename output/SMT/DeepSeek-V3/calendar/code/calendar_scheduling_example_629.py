from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Margaret's busy slots in minutes since 9:00
    margaret_busy = {
        'Monday': [
            (90, 120),   # 10:30-11:00
            (150, 180),  # 11:30-12:00
            (240, 270),  # 13:00-13:30
            (360, 480)   # 15:00-17:00
        ],
        'Tuesday': [
            (180, 210)  # 12:00-12:30
        ]
    }

    # Alexis's busy slots in minutes since 9:00
    alexis_busy = {
        'Monday': [
            (30, 150),   # 9:30-11:30
            (180, 210),  # 12:30-13:00
            (300, 480)   # 14:00-17:00
        ],
        'Tuesday': [
            (0, 30),     # 9:00-9:30
            (60, 90),    # 10:00-10:30
            (300, 450)   # 14:00-16:30
        ]
    }

    # Create a Z3 solver instance
    s = Solver()

    # The meeting day (0: Monday, 1: Tuesday)
    day = Int('day')
    s.add(day >= 0, day <= 1)

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Constraints for each day
    day_constraints = []
    days = ['Monday', 'Tuesday']
    for d in range(2):
        day_name = days[d]
        # Margaret does not want to meet on Monday and before 14:30 on Tuesday
        if day_name == 'Monday':
            continue  # Skip Monday
        elif day_name == 'Tuesday':
            margaret_free = And(is_free(meeting_start, margaret_busy[day_name]), meeting_start >= 330)  # 14:30 is 330 minutes
        
        # Alexis's free slots for the day
        alexis_free = is_free(meeting_start, alexis_busy[day_name])
        
        # Combined constraint for the day
        day_constraints.append(And(day == d, margaret_free, alexis_free))

    # Add the disjunction of all day constraints
    s.add(Or(*day_constraints))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_minutes = m[meeting_start].as_long()
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        day_name = days[day_val]
        print(f"{day_name}, {start_hour:02d}:{start_minute:02d} to {end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable meeting time found.")

find_meeting_time()