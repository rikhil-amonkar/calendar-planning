from z3 import Solver, Int, Or, Implies

# Helper functions to convert minutes to HH:MM string and day index to day name.
def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def day_to_str(day_index):
    days = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    return days[day_index]

# Create the solver.
s = Solver()

meeting_duration = 60  # Duration in minutes.

# Variables:
# day: an integer representing the day (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday)
# start: meeting start time in minutes from midnight.
day = Int('day')
start = Int('start')
end = start + meeting_duration

# Working hours are 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting must finish by 17:00 so start can be at most 960 (1020 - 60).
s.add(day >= 0, day <= 4)
s.add(start >= 540, start <= 960)
s.add(end <= 1020)

# Betty cannot meet on Wednesday or Thursday.
s.add(day != 2)  # Wednesday
s.add(day != 3)  # Thursday

# Busy intervals for each participant, with times expressed in minutes since midnight.
# Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday

# Betty's busy schedule
busy_betty = {
    0: [(600, 630), (690, 750), (960, 990)],            # Monday: 10:00-10:30, 11:30-12:30, 16:00-16:30
    1: [(570, 600), (630, 660), (720, 750), (810, 900), (990, 1020)],  # Tuesday: 9:30-10:00, 10:30-11:00, 12:00-12:30, 13:30-15:00, 16:30-17:00
    2: [(810, 840), (870, 900)],                          # Wednesday: 13:30-14:00, 14:30-15:00 (but not allowed)
    3: [],                                              # Thursday: No busy times but not allowed
    4: [(540, 600), (690, 720), (750, 780), (870, 900)]   # Friday: 9:00-10:00, 11:30-12:00, 12:30-13:00, 14:30-15:00
}

# Megan's busy schedule
busy_megan = {
    0: [(540, 1020)],                                   # Monday: 9:00-17:00 (fully booked)
    1: [(540, 570), (600, 630), (720, 840), (900, 930), (960, 990)],  # Tuesday: 9:00-9:30, 10:00-10:30, 12:00-14:00, 15:00-15:30, 16:00-16:30
    2: [(570, 630), (660, 690), (750, 780), (810, 870), (930, 1020)], # Wednesday: 9:30-10:30, 11:00-11:30, 12:30-13:00, 13:30-14:30, 15:30-17:00
    3: [(540, 630), (690, 840), (870, 900), (930, 990)],  # Thursday: 9:00-10:30, 11:30-14:00, 14:30-15:00, 15:30-16:30
    4: [(540, 1020)]                                    # Friday: 9:00-17:00 (fully booked)
}

# For each busy interval on a given day, ensure the meeting does not overlap it.
# That is, if the meeting is scheduled on a day with a busy interval, then either the meeting
# ends before that busy interval starts, or it starts after the busy interval ends.
for d in range(5):
    # Constraints for Betty's busy intervals
    for (b_start, b_end) in busy_betty.get(d, []):
        s.add(Implies(day == d, Or(end <= b_start, start >= b_end)))
    # Constraints for Megan's busy intervals
    for (b_start, b_end) in busy_megan.get(d, []):
        s.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

# Check the constraints and output the solution.
if s.check().r == 1:
    m = s.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    chosen_end = chosen_start + meeting_duration

    day_str = day_to_str(chosen_day)
    start_str = minutes_to_time_str(chosen_start)
    end_str = minutes_to_time_str(chosen_end)
    # Output in the required format: Day and time range HH:MM:HH:MM
    print(f"{day_str} {start_str}:{end_str}")
else:
    print("No solution found.")