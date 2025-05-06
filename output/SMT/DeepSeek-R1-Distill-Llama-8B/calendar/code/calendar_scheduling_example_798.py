from z3 import *

# Define the start and end times in minutes (9:00 is 0, 17:00 is 1020)
start = 0
end = 1020

# Convert blocked times to minutes
# Nancy's blocked times
nancy_block1_start = 600   # 10:00
nancy_block1_end = 630    # 10:30
nancy_block2_start = 750   # 12:30
nancy_block2_end = 780    # 13:00
nancy_block3_start = 870   # 14:30
nancy_block3_end = 990    # 16:00

# Jose's blocked times
jose_block1_start = 0     # 9:00
jose_block1_end = 1020    # 17:00
jose_block2_start = 0     # 9:00
jose_block2_end = 30      # 9:30
jose_block3_start = 60     # 10:00
jose_block3_end = 210     # 12:30
jose_block4_start = 330    # 13:30
jose_block4_end = 390     # 14:30
jose_block5_start = 450    # 15:00
jose_block5_end = 1020    # 17:00

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the variable t
t = Variable('t')

# Constraints for Nancy
s.add(t < nancy_block1_start)
s.add(t >= nancy_block1_end)
s.add(t < nancy_block2_start)
s.add(t >= nancy_block2_end)
s.add(t < nancy_block3_start)
s.add(t >= nancy_block3_end)

# Constraints for Jose
s.add(t < jose_block1_start)
s.add(t >= jose_block1_end)
s.add(t < jose_block2_start)
s.add(t >= jose_block2_end)
s.add(t < jose_block3_start)
s.add(t >= jose_block3_end)
s.add(t < jose_block4_start)
s.add(t >= jose_block4_end)
s.add(t < jose_block5_start)
s.add(t >= jose_block5_end)

# Ensure the meeting starts by 16:00 (960 minutes) and ends by 16:30 (990 minutes)
s.add(t <= 960 - meeting_duration)
s.add(t >= 0)
s.add(t <= 960)

# Solve the problem
s.solve()

# If a solution exists, print it
if s.model():
    t_val = s.model()[t]
    print(f"The meeting can be scheduled at {t_val // 60}:{t_val % 60}")
else:
    print("No solution found")