from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Cheryl's busy slots in minutes since 9:00 for each day
    cheryl_busy = {
        'Monday': [
            (0, 30),      # 9:00-9:30
            (150, 240),    # 11:30-13:00
            (390, 420)     # 15:30-16:00
        ],
        'Tuesday': [
            (360, 390)     # 15:00-15:30
        ],
        'Wednesday': []    # Cannot meet on Wednesday
    }

    # Kyle's busy slots in minutes since 9:00 for each day
    kyle_busy = {
        'Monday': [
            (0, 480)      # 9:00-17:00
        ],
        'Tuesday': [
            (30, 480)     # 9:30-17:00
        ],
        'Wednesday': [
            (0, 30),      # 9:00-9:30
            (60, 240),    # 10:00-13:00
            (270, 300),   # 13:30-14:00
            (330, 480)    # 14:30-17:00
        ]
    }

    # Create a Z3 solver instance
    s = Solver()

    # The meeting day (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(Or(day == 0, day == 1))  # Exclude Wednesday (day == 2)

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Constraints for each day (Monday and Tuesday)
    day_constraints = []
    days = ['Monday', 'Tuesday']
    for d in range(2):
        day_name = days[d]
        # Cheryl's free slots for the day
        cheryl_free = is_free(meeting_start, cheryl_busy[day_name])
        # Kyle's free slots for the day
        kyle_free = is_free(meeting_start, kyle_busy[day_name])
        # Combined constraint for the day
        day_constraints.append(And(day == d, cheryl_free, kyle_free))

    # Add the disjunction of all day constraints
    s.add(Or(*day_constraints))

    # To find the earliest time, we minimize the start time
    # This is done by checking satisfiability with increasing start times
    earliest_start = None
    for start in range(0, work_end - work_start - meeting_duration + 1, 30):
        s.push()
        s.add(meeting_start == start)
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
            return
        s.pop()

    print("No suitable meeting time found.")

find_meeting_time()