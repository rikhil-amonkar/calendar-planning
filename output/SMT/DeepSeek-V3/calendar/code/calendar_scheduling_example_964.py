from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 60 minutes

    # Betty's busy slots in minutes since 9:00 for each day
    betty_busy = {
        'Monday': [
            (60, 90),    # 10:00-10:30
            (150, 210),   # 11:30-12:30
            (420, 450)    # 16:00-16:30
        ],
        'Tuesday': [
            (30, 60),     # 9:30-10:00
            (90, 120),    # 10:30-11:00
            (180, 210),   # 12:00-12:30
            (270, 360),   # 13:30-15:00
            (450, 480)    # 16:30-17:00
        ],
        'Friday': [
            (0, 60),      # 9:00-10:00
            (150, 180),   # 11:30-12:00
            (210, 240),   # 12:30-13:00
            (330, 360)    # 14:30-15:00
        ]
    }

    # Megan's busy slots in minutes since 9:00 for each day
    megan_busy = {
        'Monday': [
            (0, 480)      # 9:00-17:00
        ],
        'Tuesday': [
            (0, 30),      # 9:00-9:30
            (60, 90),     # 10:00-10:30
            (180, 300),   # 12:00-14:00
            (360, 390),   # 15:00-15:30
            (420, 450)    # 16:00-16:30
        ],
        'Wednesday': [
            (30, 90),     # 9:30-10:30
            (120, 150),   # 11:00-11:30
            (210, 240),   # 12:30-13:00
            (270, 330),   # 13:30-14:30
            (390, 480)    # 15:30-17:00
        ],
        'Thursday': [
            (0, 90),      # 9:00-10:30
            (150, 300),   # 11:30-14:00
            (330, 360),   # 14:30-15:00
            (390, 450)    # 15:30-16:30
        ],
        'Friday': [
            (0, 480)      # 9:00-17:00
        ]
    }

    # Create a Z3 solver instance
    s = Solver()

    # The meeting day (0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday)
    day = Int('day')
    s.add(day >= 0, day <= 4)

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Constraints for each day
    day_constraints = []
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    for d in range(5):
        day_name = days[d]
        # Betty cannot meet on Wednesday or Thursday
        if day_name in ['Wednesday', 'Thursday']:
            continue
        
        # Betty's free slots for the day
        betty_free = is_free(meeting_start, betty_busy.get(day_name, []))
        
        # Megan's free slots for the day
        megan_free = is_free(meeting_start, megan_busy.get(day_name, []))
        
        # Combined constraint for the day
        day_constraints.append(And(day == d, betty_free, megan_free))

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