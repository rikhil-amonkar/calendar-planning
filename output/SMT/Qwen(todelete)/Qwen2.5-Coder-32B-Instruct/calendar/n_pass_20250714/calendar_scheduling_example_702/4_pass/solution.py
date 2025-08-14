from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Constants for the duration of the meeting and the work hours
meeting_duration = 30  # 30 minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the constraints for Robert's schedule
robert_busy_times = [
    (11 * 60, 11 * 60 + 30),  # Monday 11:00 - 11:30
    (14 * 60, 14 * 60 + 30),  # Monday 14:00 - 14:30
    (15 * 60 + 30, 16 * 60),  # Monday 15:30 - 16:00
    (10 * 60 + 30, 11 * 60),  # Tuesday 10:30 - 11:00
    (15 * 60, 15 * 60 + 30),  # Tuesday 15:00 - 15:30
    (10 * 60, 11 * 60),       # Wednesday 10:00 - 11:00
    (11 * 60 + 30, 12 * 60),  # Wednesday 11:30 - 12:00
    (12 * 60 + 30, 13 * 60),  # Wednesday 12:30 - 13:00
    (13 * 60 + 30, 14 * 60),  # Wednesday 13:30 - 14:00
    (15 * 60, 15 * 60 + 30),  # Wednesday 15:00 - 15:30
    (16 * 60, 16 * 60 + 30)   # Wednesday 16:00 - 16:30
]

# Define the constraints for Ralph's schedule
ralph_busy_times = [
    (10 * 60, 13 * 60 + 30),  # Monday 10:00 - 13:30
    (14 * 60, 14 * 60 + 30),  # Monday 14:00 - 14:30
    (15 * 60, 17 * 60),       # Monday 15:00 - 17:00
    (9 * 60, 9 * 60 + 30),    # Tuesday 9:00 - 9:30
    (10 * 60, 10 * 60 + 30),  # Tuesday 10:00 - 10:30
    (11 * 60, 11 * 60 + 30),  # Tuesday 11:00 - 11:30
    (12 * 60, 13 * 60),       # Tuesday 12:00 - 13:00
    (14 * 60, 15 * 60 + 30),  # Tuesday 14:00 - 15:30
    (16 * 60, 17 * 60),       # Tuesday 16:00 - 17:00
    (10 * 60 + 30, 11 * 60),  # Wednesday 10:30 - 11:00
    (11 * 60 + 30, 12 * 60),  # Wednesday 11:30 - 12:00
    (13 * 60, 14 * 60 + 30),  # Wednesday 13:00 - 14:30
    (16 * 60 + 30, 17 * 60)   # Wednesday 16:30 - 17:00
]

# Create a solver instance
s = Optimize()

# Add constraints for the day
s.add(day >= 0, day <= 2)

# Add constraints for the start time
s.add(start_time >= work_start, start_time <= work_end - meeting_duration)

# Function to check if a time slot is busy
def is_busy(time_slot, busy_times):
    return Or([And(day == d, start_time >= bs, start_time < be) for d, bs, be in busy_times])

# Add constraints for Robert's busy times
robert_busy_times_with_days = [(0, bs, be) for bs, be in robert_busy_times] + \
                              [(1, bs, be) for bs, be in robert_busy_times] + \
                              [(2, bs, be) for bs, be in robert_busy_times]
s.add(Not(is_busy((day, start_time, start_time + meeting_duration), robert_busy_times_with_days)))

# Add constraints for Ralph's busy times
ralph_busy_times_with_days = [(0, bs, be) for bs, be in ralph_busy_times] + \
                             [(1, bs, be) for bs, be in ralph_busy_times] + \
                             [(2, bs, be) for bs, be in ralph_busy_times]
s.add(Not(is_busy((day, start_time, start_time + meeting_duration), ralph_busy_times_with_days)))

# Robert would like to avoid more meetings on Monday, so we add a penalty for Monday
penalty = If(day == 0, 1, 0)
s.minimize(penalty)

# Check if there is a solution
if s.check() == sat:
    m = s.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday"][m[day].as_long()]
    meeting_start_time = m[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time // 60}:{meeting_start_time % 60:02d}")
    print(f"End Time: {meeting_end_time // 60}:{meeting_end_time % 60:02d}")
else:
    print("No solution found")