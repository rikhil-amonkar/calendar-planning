from z3 import *

# Define the day
day = 'Monday'

# Define the start and end times
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes

# Define the duration of the meeting
duration = 30

# Define the constraints for each participant
tyler = [start_time, end_time]
kelly = [start_time, end_time]
stephanie = [900, 1130, 1430, 1500]
hannah = [start_time, end_time]
joe = [900, 930, 1000, 1200, 1230, 1300, 1400, 1700]
diana = [900, 1030, 1130, 1200, 1300, 1430, 1530, 1600, 1700]
deborah = [900, 1000, 1030, 1200, 1230, 1300, 1330, 1400, 1530, 1630, 1700]

# Define the solver
s = Solver()

# Define the variables
t = Int('t')

# Define the constraints
s.add(t >= start_time)
s.add(t + duration <= end_time)
s.add(t % 60 == 0)  # The start time must be on the hour
s.add(Not(t in stephanie))
s.add(Not(t in joe))
s.add(Not(t in diana))
s.add(Not(t in deborah))

# Check if a solution exists
if s.check() == sat:
    model = s.model()
    t_value = model[t]
    start_hour = t_value // 60
    start_minute = t_value % 60
    end_hour = (t_value + duration) // 60
    end_minute = (t_value + duration) % 60

    # Print the solution
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
    print(f"End Time: {end_hour:02d}:{end_minute:02d}")
else:
    print("No solution exists.")