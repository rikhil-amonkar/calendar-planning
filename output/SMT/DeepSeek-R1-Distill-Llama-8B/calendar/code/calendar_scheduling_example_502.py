from z3 import *

# Define the start and end times in minutes (9:00 is 0, 17:00 is 1020)
start = 0
end = 1020

# Convert blocked times to minutes
# Jack's blocked times
jack_block1_start = 690   # 9:30
jack_block1_end = 720    # 10:30
jack_block2_start = 750   # 12:30
jack_block2_end = 780    # 13:00
jack_block3_start = 840   # 14:00
jack_block3_end = 870    # 14:30
jack_block4_start = 960   # 16:00
jack_block4_end = 990    # 16:30

# Charlotte's blocked times
charlotte_block1_start = 690   # 9:30
charlotte_block1_end = 720    # 10:00
charlotte_block2_start = 750   # 12:00
charlotte_block2_end = 780    # 13:00
charlotte_block3_start = 870   # 14:00
charlotte_block3_end = 990    # 16:00

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the variable t
t = Variable('t')

# Constraints for Jack
s.add(t < jack_block1_start)
s.add(t >= jack_block1_end)
s.add(t < jack_block2_start)
s.add(t >= jack_block2_end)
s.add(t < jack_block3_start)
s.add(t >= jack_block3_end)
s.add(t < jack_block4_start)
s.add(t >= jack_block4_end)

# Constraints for Charlotte
s.add(t < charlotte_block1_start)
s.add(t >= charlotte_block1_end)
s.add(t < charlotte_block2_start)
s.add(t >= charlotte_block2_end)
s.add(t < charlotte_block3_start)
s.add(t >= charlotte_block3_end)

# Solve the problem
s.solve()

# If a solution exists, print it
if s.model():
    t_val = s.model()[t]
    print(f"The meeting can be scheduled at {t_val // 60}:{t_val % 60}")
else:
    print("No solution found")