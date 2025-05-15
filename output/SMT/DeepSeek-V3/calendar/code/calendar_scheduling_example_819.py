from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Ruth's busy slots in minutes since 9:00 for each day
    ruth_busy = {
        'Monday': [
            (0, 480)      # 9:00-17:00
        ],
        'Tuesday': [
            (0, 480)      # 9:00-17:00
        ],
        'Wednesday': [
            (0, 480)      # 9:00-17:00
        ],
        'Thursday': [
            (0, 120),     # 9:00-11:00
            (150, 330),    # 11:30-14:30
            (360, 480)     # 15:00-17:00
        ]
    }

    # Create a Z3 solver instance
    s = Solver()

    # The meeting day (0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday)
    day = Int('day')
    s.add(day >= 0, day <= 3)

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Constraints for each day
    day_constraints = []
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    for d in range(4):
        day_name = days[d]
        # Julie is free all week but prefers to avoid Thursday before 11:30 (150 minutes since 9:00)
        if day_name == 'Thursday':
            julie_free = meeting_start >= 150
        else:
            julie_free = True
        
        # Ruth's free slots for the day
        ruth_free = is_free(meeting_start, ruth_busy[day_name])
        
        # Combined constraint for the day
        day_constraints.append(And(day == d, julie_free, ruth_free))

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