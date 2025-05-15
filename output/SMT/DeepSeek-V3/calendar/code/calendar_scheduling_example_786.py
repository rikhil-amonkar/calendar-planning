from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Amy's busy slots in minutes since 9:00 for Wednesday
    amy_busy = {
        'Wednesday': [
            (120, 150),     # 11:00-11:30
            (270, 300)      # 13:30-14:00
        ]
    }

    # Pamela's busy slots in minutes since 9:00 for each day
    pamela_busy = {
        'Monday': [
            (0, 90),        # 9:00-10:30
            (120, 450)      # 11:00-16:30
        ],
        'Tuesday': [
            (0, 30),        # 9:00-9:30
            (60, 480)       # 10:00-17:00
        ],
        'Wednesday': [
            (0, 30),        # 9:00-9:30
            (60, 120),      # 10:00-11:00
            (150, 270),     # 11:30-13:30
            (330, 360),    # 14:30-15:00
            (420, 450)     # 16:00-16:30
        ]
    }

    # Create a Z3 solver instance
    s = Solver()

    # The meeting day (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Constraints for each day
    day_constraints = []
    days = ['Monday', 'Tuesday', 'Wednesday']
    for d in range(3):
        day_name = days[d]
        # Amy's free slots for the day (only Wednesday has constraints)
        if day_name == 'Wednesday':
            amy_free = is_free(meeting_start, amy_busy[day_name])
        else:
            amy_free = True  # Amy is free on Monday and Tuesday
        
        # Pamela's free slots for the day
        pamela_free = is_free(meeting_start, pamela_busy[day_name])
        
        # Additional constraints based on Pamela's preferences
        if day_name == 'Monday':
            # Avoid Monday
            continue
        elif day_name == 'Tuesday':
            # Avoid before 16:00 (420 minutes since 9:00)
            pamela_free = And(pamela_free, meeting_start >= 420)
        elif day_name == 'Wednesday':
            # Avoid before 16:00 (420 minutes since 9:00)
            pamela_free = And(pamela_free, meeting_start >= 420)
        
        # Combined constraint for the day
        day_constraints.append(And(day == d, amy_free, pamela_free))

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