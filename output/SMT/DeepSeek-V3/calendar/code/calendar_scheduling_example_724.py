from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Tyler's busy slots in minutes since 9:00 for each day
    tyler_busy = {
        'Tuesday': [
            (0, 30),        # 9:00-9:30
            (330, 360)      # 14:30-15:00
        ],
        'Wednesday': [
            (90, 120),      # 10:30-11:00
            (210, 240),     # 12:30-13:00
            (270, 300),     # 13:30-14:00
            (450, 480)      # 16:30-17:00
        ]
    }

    # Ruth's busy slots in minutes since 9:00 for each day
    ruth_busy = {
        'Monday': [
            (0, 60),        # 9:00-10:00
            (90, 180),      # 10:30-12:00
            (210, 330),     # 12:30-14:30
            (360, 420),     # 15:00-16:00
            (450, 480)      # 16:30-17:00
        ],
        'Tuesday': [
            (0, 480)        # 9:00-17:00
        ],
        'Wednesday': [
            (0, 480)        # 9:00-17:00
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
        # Tyler's free slots for the day
        if day_name in tyler_busy:
            tyler_free = is_free(meeting_start, tyler_busy[day_name])
        else:
            tyler_free = True  # Tyler is free on Monday
        
        # Ruth's free slots for the day
        ruth_free = is_free(meeting_start, ruth_busy[day_name])
        
        # Additional constraints based on Tyler's preferences
        if day_name == 'Monday':
            # Avoid before 16:00 (420 minutes since 9:00)
            tyler_free = And(tyler_free, meeting_start >= 420)
        
        # Combined constraint for the day
        day_constraints.append(And(day == d, tyler_free, ruth_free))

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