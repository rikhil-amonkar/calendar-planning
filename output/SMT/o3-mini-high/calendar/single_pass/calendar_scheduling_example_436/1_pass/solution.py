from z3 import Int, Solver, Or

# Define meeting parameters
meeting_duration = 30  # minutes
work_start = 9 * 60    # 9:00 in minutes (540)
work_end = 17 * 60     # 17:00 in minutes (1020)

# Create the Z3 solver instance
solver = Solver()

# Meeting start time as an integer representing minutes since midnight.
s = Int('s')

# Meeting must be within work hours: s >= 9:00 and s+30 <= 17:00.
solver.add(s >= work_start, s + meeting_duration <= work_end)

# Busy intervals for each participant are given as (start, end) in minutes.
busy_intervals = [
    # Patrick
    (13 * 60 + 30, 14 * 60),   # 13:30 - 14:00
    (14 * 60 + 30, 15 * 60),    # 14:30 - 15:00

    # Shirley
    (9 * 60, 9 * 60 + 30),      # 9:00 - 9:30
    (11 * 60, 11 * 60 + 30),    # 11:00 - 11:30
    (12 * 60, 12 * 60 + 30),    # 12:00 - 12:30
    (14 * 60 + 30, 15 * 60),    # 14:30 - 15:00
    (16 * 60, 17 * 60),         # 16:00 - 17:00

    # Jeffrey
    (9 * 60, 9 * 60 + 30),      # 9:00 - 9:30
    (10 * 60 + 30, 11 * 60),     # 10:30 - 11:00
    (11 * 60 + 30, 12 * 60),     # 11:30 - 12:00
    (13 * 60, 13 * 60 + 30),     # 13:00 - 13:30
    (16 * 60, 17 * 60),         # 16:00 - 17:00

    # Gloria
    (11 * 60 + 30, 12 * 60),     # 11:30 - 12:00
    (15 * 60, 15 * 60 + 30),     # 15:00 - 15:30

    # Nathan
    (9 * 60, 9 * 60 + 30),       # 9:00 - 9:30
    (10 * 60 + 30, 12 * 60),      # 10:30 - 12:00
    (14 * 60, 17 * 60),          # 14:00 - 17:00

    # Angela
    (9 * 60, 9 * 60 + 30),       # 9:00 - 9:30
    (10 * 60, 11 * 60),          # 10:00 - 11:00
    (12 * 60 + 30, 15 * 60),     # 12:30 - 15:00
    (15 * 60 + 30, 16 * 60 + 30),# 15:30 - 16:30

    # David
    (9 * 60, 9 * 60 + 30),       # 9:00 - 9:30
    (10 * 60, 10 * 60 + 30),     # 10:00 - 10:30
    (11 * 60, 14 * 60),          # 11:00 - 14:00
    (14 * 60 + 30, 16 * 60 + 30)  # 14:30 - 16:30
]

# For each busy interval, ensure that the meeting (s, s+30) does NOT overlap with it.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(s + meeting_duration <= busy_start, s >= busy_end))

# Check if a solution exists and print it in the required format.
if solver.check() == "sat":
    model = solver.model()
    start_time = model[s].as_long()  # Meeting start time in minutes since midnight.
    end_time = start_time + meeting_duration

    # Convert minutes to HH:MM format.
    def minutes_to_time(m):
        hour = m // 60
        minute = m % 60
        return f"{hour:02d}:{minute:02d}"

    solution_string = (
        "SOLUTION:\n"
        "Day: Monday\n"
        f"Start Time: {minutes_to_time(start_time)}\n"
        f"End Time: {minutes_to_time(end_time)}"
    )
    print(solution_string)
else:
    print("No solution found.")