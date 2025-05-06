from z3 import *

# Define the start and end times in minutes (9:00 is 0, 17:00 is 1020)
start = 0
end = 1020

# Albert's blocked times
albert_block1_start = 600   # 10:00
albert_block1_end = 630    # 10:30
albert_block2_start = 660   # 11:00
albert_block2_end = 720     # 12:00

# Albert can't meet after 11:00, so the latest start time is 11:00 (660 minutes)
# The meeting duration is 30 minutes

# Define the variable t
t = Variable('t')

# Constraints
# The meeting must start before 11:00 (660 minutes) and end by 11:30 (690 minutes)
# So, t <= 660 and t + 30 <= 690
s = Solver()

s.add(t <= 660)
s.add(t >= 660 - 30)  # t >= 630 (10:30)
s.add(t >= 0)
s.add(t <= 660)

# Solve the problem
s.solve()

# If a solution exists, print it
if s.model():
    t_val = s.model()[t]
    print(f"The meeting can be scheduled at {t_val // 60}:{t_val % 60}")
else:
    print("No solution found")