YOUR_CODE
from z3 import *

# Define the variables
times = [0] * 13
meetings = [0] * 13
distances = [
    15, 16, 22, 6, 12, 21, 10, 13, 15,
    16, 13, 23, 16, 22, 9, 26, 17,
    16, 11, 19, 21, 19, 17, 8, 21, 7,
    23, 22, 19, 27, 18, 27, 19, 22, 16,
    15, 22, 17, 15, 18, 27, 30, 15, 14,
    21, 11, 17, 22, 21, 30, 17, 30, 25,
    10, 9, 8, 16, 15, 14, 16, 17, 17,
    13, 23, 20, 19, 15, 9, 30, 17, 15
]

# Define the constraints
s = Optimize()
for i in range(13):
    times[i] = Int(f"time_{i}")
    s.add(times[i] >= 0)
    s.add(times[i] <= 24 * 60)  # 24 hours

s.add(times[0] == 0)  # You arrive at Pacific Heights at 9:00AM

# Meet Helen for a minimum of 45 minutes
s.add(If(times[1] > times[0] + distances[0], times[1] - 45, times[0] + distances[0] - times[1]) >= 0)

# Meet Steven for a minimum of 105 minutes
s.add(If(times[6] > times[0] + distances[1], times[6] - 105, times[0] + distances[1] - times[6]) >= 0)

# Meet Deborah for a minimum of 30 minutes
s.add(If(times[2] > times[0] + distances[2], times[2] - 30, times[0] + distances[2] - times[2]) >= 0)

# Meet Matthew for a minimum of 45 minutes
s.add(If(times[4] > times[0] + distances[3], times[4] - 45, times[0] + distances[3] - times[4]) >= 0)

# Meet Joseph for a minimum of 120 minutes
s.add(If(times[8] > times[0] + distances[4], times[8] - 120, times[0] + distances[4] - times[8]) >= 0)

# Meet Ronald for a minimum of 60 minutes
s.add(If(times[9] > times[0] + distances[5], times[9] - 60, times[0] + distances[5] - times[9]) >= 0)

# Meet Robert for a minimum of 120 minutes
s.add(If(times[10] > times[0] + distances[6], times[10] - 120, times[0] + distances[6] - times[10]) >= 0)

# Meet Rebecca for a minimum of 30 minutes
s.add(If(times[11] > times[0] + distances[7], times[11] - 30, times[0] + distances[7] - times[11]) >= 0)

# Meet Elizabeth for a minimum of 120 minutes
s.add(If(times[12] > times[0] + distances[8], times[12] - 120, times[0] + distances[8] - times[12]) >= 0)

# Solve the optimization problem
result = s.check()

if result == sat:
    model = s.model()
    for i in range(13):
        print(f"Time at {i}: {model[times[i]].as_long()} minutes")
        meetings[i] = model[times[i]].as_long()
    print("Meetings:")
    for i in range(13):
        if meetings[i]!= 0:
            print(f"Meet at {i} for {distances[i]} minutes")
else:
    print("No solution found")