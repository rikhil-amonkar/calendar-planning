from z3 import *

# Define the start and end times in minutes (9:00 is 0, 17:00 is 1020)
start = 0
end = 1020

# Convert blocked times to minutes
# Harold's blocked times on Monday
harold_monday_block1_start = 600   # 10:00
harold_monday_block1_end = 630    # 10:30
harold_monday_block2_start = 690   # 11:00
harold_monday_block2_end = 1020   # 17:00

# Harold's blocked times on Tuesday
harold_tuesday_block1_start = 0     # 9:00
harold_tuesday_block1_end = 30     # 9:30
harold_tuesday_block2_start = 660   # 11:00
harold_tuesday_block2_end = 690    # 11:30
harold_tuesday_block3_start = 750   # 12:30
harold_tuesday_block3_end = 780    # 13:00
harold_tuesday_block4_start = 870   # 14:30
harold_tuesday_block4_end = 990    # 16:30
harold_tuesday_block5_start = 1020   # 17:00

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the variable t
t = Variable('t')

# Constraints for Harold
# On Monday:
# Meeting cannot be scheduled during his busy blocks
s.add(t < harold_monday_block1_start)
s.add(t >= harold_monday_block1_end)
s.add(t < harold_monday_block2_start)
s.add(t >= harold_monday_block2_end)

# On Tuesday:
# Meeting cannot be scheduled during his busy blocks
s.add(t < harold_tuesday_block1_start)
s.add(t >= harold_tuesday_block1_end)
s.add(t < harold_tuesday_block2_start)
s.add(t >= harold_tuesday_block2_end)
s.add(t < harold_tuesday_block3_start)
s.add(t >= harold_tuesday_block3_end)
s.add(t < harold_tuesday_block4_start)
s.add(t >= harold_tuesday_block4_end)
s.add(t < harold_tuesday_block5_start)
s.add(t >= harold_tuesday_block5_end)

# Additionally, Harold wants to avoid meetings on Monday and prefers Tuesday before 14:30 (870 minutes)
# So, the meeting must be on Tuesday and before 870 minutes (14:30)
s.add(t >= harold_tuesday_block1_end)  # t >= 30 (9:30)
s.add(t <= harold_tuesday_block4_start - meeting_duration)  # t <= 870 - 30 = 840 (14:00)

# Solve the problem
s.solve()

# If a solution exists, print it
if s.model():
    t_val = s.model()[t]
    print(f"The meeting can be scheduled at {t_val // 60}:{t_val % 60}")
else:
    print("No solution found")