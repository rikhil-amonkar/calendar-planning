from z3 import *

# Helper functions to convert time strings (HH:MM) to minutes and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # 30 minutes meeting
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Days encoding: 0 = Monday, 1 = Tuesday.
# According to Margaret's preference, she does not want a meeting on Monday.
# Thus, the meeting must be scheduled on Tuesday.
# Furthermore, on Tuesday Margaret prefers not to meet before 14:30.
preferred_tuesday_start = time_to_minutes("14:30")  # 870 minutes

# Busy intervals for each participant (day-specific):

# Margaret's busy intervals.
margaret_busy = {
    0: [  # Monday (won't be used because Margaret doesn't want Monday)
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("12:00"), time_to_minutes("12:30"))
    ]
}

# Alexis's busy intervals.
alexis_busy = {
    0: [  # Monday
        (time_to_minutes("9:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("17:00"))
    ],
    1: [  # Tuesday
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("14:00"), time_to_minutes("16:30"))
    ]
}

# Create Z3 Solver.
s = Solver()

# Define the day variable: meeting_day is an integer, either 0 (Monday) or 1 (Tuesday)
meeting_day = Int("meeting_day")
s.add(Or(meeting_day == 0, meeting_day == 1))

# Define the meeting start time variable (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must be scheduled within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: According to Margaret's preference:
#   - No meeting on Monday
#   - On Tuesday, meeting cannot start before 14:30
s.add(meeting_day == 1)
s.add(meeting_start >= preferred_tuesday_start)

# Helper function to add busy constraints for a participant.
def add_busy_constraints(busy_dict):
    for day, intervals in busy_dict.items():
        for (busy_start, busy_end) in intervals:
            # If meeting is on the same day, it must not overlap with a busy interval.
            s.add(Implies(meeting_day == day, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Add busy constraints for Margaret and Alexis.
add_busy_constraints(margaret_busy)
add_busy_constraints(alexis_busy)

# Check the satisfiability and print a solution.
if s.check() == sat:
    m = s.model()
    day_val = m[meeting_day].as_long()
    start_val = m[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_name = {0: "Monday", 1: "Tuesday"}[day_val]
    
    print("A possible meeting time:")
    print("Day:   ", day_name)
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")