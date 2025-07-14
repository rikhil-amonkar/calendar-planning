from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Constants for the time range in minutes from 00:00
nine_am = 9 * 60
five_pm = 17 * 60
half_hour = 30

# Constraints for Jesse's schedule
jesse_busy_monday = Or(
    And(start_time >= 13 * 60 + 30, start_time < 14 * 60),
    And(start_time >= 14 * 60 + 30, start_time < 15 * 60)
)

jesse_busy_tuesday = Or(
    And(start_time >= 9 * 60, start_time < 9 * 60 + 30),
    And(start_time >= 13 * 60, start_time < 13 * 60 + 30),
    And(start_time >= 14 * 60, start_time < 15 * 60)
)

# Constraints for Lawrence's schedule
lawrence_busy_monday = True  # Lawrence is busy all day on Monday

lawrence_busy_tuesday = Or(
    And(start_time >= 9 * 60 + 30, start_time < 10 * 60 + 30),
    And(start_time >= 11 * 60 + 30, start_time < 12 * 60 + 30),
    And(start_time >= 13 * 60, start_time < 13 * 60 + 30),
    And(start_time >= 14 * 60 + 30, start_time < 15 * 60),
    And(start_time >= 15 * 60 + 30, start_time < 16 * 60 + 30)
)

# Additional constraint for Lawrence that he cannot meet on Tuesday after 16:30
lawrence_tuesday_constraint = Implies(day == 1, start_time + half_hour <= 16 * 60 + 30)

# General constraints
day_constraint = Or(day == 0, day == 1)
time_constraint = And(start_time >= nine_am, start_time + half_hour <= five_pm)

# Solver setup
s = Solver()
s.add(day_constraint)
s.add(time_constraint)
s.add(Not(jesse_busy_monday))
s.add(Not(jesse_busy_tuesday))
s.add(Or(day == 1, Not(lawrence_busy_monday)))
s.add(Not(lawrence_busy_tuesday))
s.add(lawrence_tuesday_constraint)

# Check if there is a solution
if s.check() == sat:
    m = s.model()
    meeting_day = "Monday" if m[day].as_long() == 0 else "Tuesday"
    meeting_start_time = m[start_time].as_long()
    meeting_end_time = meeting_start_time + half_hour

    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time // 60}:{meeting_start_time % 60:02d}")
    print(f"End Time: {meeting_end_time // 60}:{meeting_end_time % 60:02d}")
else:
    print("No solution found")