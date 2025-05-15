from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Robert's busy slots in minutes since 9:00 for each day
    robert_busy = {
        'Monday': [
            (120, 150),   # 11:00-11:30
            (300, 330),   # 14:00-14:30
            (390, 420)    # 15:30-16:00
        ],
        'Tuesday': [
            (90, 120),    # 10:30-11:00
            (360, 390)    # 15:00-15:30
        ],
        'Wednesday': [
            (60, 120),    # 10:00-11:00
            (150, 180),   # 11:30-12:00
            (210, 240),   # 12:30-13:00
            (270, 300),    # 13:30-14:00
            (360, 390),   # 15:00-15:30
            (420, 450)    # 16:00-16:30
        ]
    }

    # Ralph's busy slots in minutes since 9:00 for each day
    ralph_busy = {
        'Monday': [
            (60, 270),    # 10:00-13:30
            (300, 330),   # 14:00-14:30
            (360, 480)    # 15:00-17:00
        ],
        'Tuesday': [
            (0, 30),      # 9:00-9:30
            (60, 90),     # 10:00-10:30
            (120, 150),   # 11:00-11:30
            (180, 240),   # 12:00-13:00
            (300, 390),   # 14:00-15:30
            (420, 480)    # 16:00-17:00
        ],
        'Wednesday': [
            (90, 120),    # 10:30-11:00
            (150, 180),   # 11:30-12:00
            (240, 330),   # 13:00-14:30
            (450, 480)    # 16:30-17:00
        ]
    }

    # Create a Z3 solver instance
    s = Solver()

    # The meeting day (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 1, day <= 2)  # Robert avoids Monday (day=0)

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
    for d in range(1, 3):  # Skip Monday (day=0)
        day_name = days[d]
        # Robert's free slots for the day
        robert_free = is_free(meeting_start, robert_busy[day_name])
        
        # Ralph's free slots for the day
        ralph_free = is_free(meeting_start, ralph_busy[day_name])
        
        # Combined constraint for the day
        day_constraints.append(And(day == d, robert_free, ralph_free))

    # Add the disjunction of all day constraints
    s.add(Or(*day_constraints))

    # To find the earliest possible meeting time, we minimize the start time
    s.minimize(meeting_start)

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