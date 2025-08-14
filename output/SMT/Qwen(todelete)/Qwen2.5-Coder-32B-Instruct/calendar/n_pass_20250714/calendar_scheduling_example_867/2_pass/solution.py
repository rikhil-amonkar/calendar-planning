from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday, 4 for Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constants for days and times
MONDAY = 1
TUESDAY = 2
WEDNESDAY = 3
THURSDAY = 4
MEETING_DURATION = 30  # 30 minutes
WORK_START = 9 * 60  # 9:00 in minutes
WORK_END = 17 * 60  # 17:00 in minutes

# Define the constraints
solver = Solver()

# Day constraints
solver.add(day >= MONDAY)
solver.add(day <= THURSDAY)

# Start time constraints within work hours
solver.add(start_time >= WORK_START)
solver.add(start_time + MEETING_DURATION <= WORK_END)

# Betty's availability
betty_busy_times = {
    MONDAY: [(10*60, 10*60+30), (13*60+30, 14*60), (15*60, 15*60+30), (16*60, 16*60+30)],
    TUESDAY: [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)],
    WEDNESDAY: [(9*60+30, 10*60), (13*60, 13*60+30), (14*60, 14*60+30)],
    THURSDAY: [(9*60+30, 10*60), (11*60+30, 12*60), (14*60, 14*60+30), (15*60, 15*60+30), (16*60+30, 17*60)]
}

for d, times in betty_busy_times.items():
    for s, e in times:
        solver.add(Or(day != d, Or(start_time >= e, start_time + MEETING_DURATION <= s)))

# Scott's availability
scott_busy_times = {
    MONDAY: [(9*60+30, 15*60), (15*60+30, 16*60), (16*60+30, 17*60)],
    TUESDAY: [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (14*60, 15*60), (16*60, 16*60+30)],
    WEDNESDAY: [(9*60+30, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
    THURSDAY: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (12*60+30, 13*60), (15*60, 16*60), (16*60+30, 17*60)]
}

for d, times in scott_busy_times.items():
    for s, e in times:
        solver.add(Or(day != d, Or(start_time >= e, start_time + MEETING_DURATION <= s)))

# Additional constraints
# Betty cannot meet on Monday
solver.add(day != MONDAY)

# Scott prefers not to meet on Wednesday, so we try to avoid it
# We will check for solutions without Wednesday first
solver.add(day != WEDNESDAY)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + MEETING_DURATION

    # Convert back to human-readable format
    days_map = {MONDAY: "Monday", TUESDAY: "Tuesday", WEDNESDAY: "Wednesday", THURSDAY: "Thursday"}
    start_hour = meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = meeting_end_time // 60
    end_minute = meeting_end_time % 60

    print(f"SOLUTION:")
    print(f"Day: {days_map[meeting_day]}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    # If no solution without Wednesday, allow Wednesday
    solver.reset()
    solver.add(day >= MONDAY)
    solver.add(day <= THURSDAY)
    solver.add(start_time >= WORK_START)
    solver.add(start_time + MEETING_DURATION <= WORK_END)
    
    for d, times in betty_busy_times.items():
        for s, e in times:
            solver.add(Or(day != d, Or(start_time >= e, start_time + MEETING_DURATION <= s)))
    
    for d, times in scott_busy_times.items():
        for s, e in times:
            solver.add(Or(day != d, Or(start_time >= e, start_time + MEETING_DURATION <= s)))
    
    solver.add(day != MONDAY)
    
    if solver.check() == sat:
        model = solver.model()
        meeting_day = model[day].as_long()
        meeting_start_time = model[start_time].as_long()
        meeting_end_time = meeting_start_time + MEETING_DURATION

        # Convert back to human-readable format
        days_map = {MONDAY: "Monday", TUESDAY: "Tuesday", WEDNESDAY: "Wednesday", THURSDAY: "Thursday"}
        start_hour = meeting_start_time // 60
        start_minute = meeting_start_time % 60
        end_hour = meeting_end_time // 60
        end_minute = meeting_end_time % 60

        print(f"SOLUTION:")
        print(f"Day: {days_map[meeting_day]}")
        print(f"Start Time: {start_hour:02}:{start_minute:02}")
        print(f"End Time: {end_hour:02}:{end_minute:02}")
    else:
        print("No solution found")