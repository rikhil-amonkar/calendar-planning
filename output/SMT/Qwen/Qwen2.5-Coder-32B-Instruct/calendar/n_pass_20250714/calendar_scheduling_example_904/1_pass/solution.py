from z3 import *

# Define the variables for the day and time
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
day = Int('day')
start_time = Int('start_time')

# Define the constraints
constraints = []

# Map days to integers for easier handling
day_map = {d: i for i, d in enumerate(days)}

# Constraints for Daniel's availability
daniel_busy = [
    (day_map["Monday"], 930, 1030),
    (day_map["Monday"], 1200, 1230),
    (day_map["Monday"], 1300, 1400),
    (day_map["Monday"], 1430, 1500),
    (day_map["Monday"], 1530, 1600),
    (day_map["Tuesday"], 1100, 1200),
    (day_map["Tuesday"], 1300, 1330),
    (day_map["Tuesday"], 1530, 1600),
    (day_map["Tuesday"], 1630, 1700),
    (day_map["Wednesday"], 900, 1000),
    (day_map["Wednesday"], 1400, 1430),
    (day_map["Thursday"], 1030, 1100),
    (day_map["Thursday"], 1200, 1300),
    (day_map["Thursday"], 1430, 1500),
    (day_map["Thursday"], 1530, 1600),
    (day_map["Friday"], 900, 930),
    (day_map["Friday"], 1130, 1200),
    (day_map["Friday"], 1300, 1330),
    (day_map["Friday"], 1630, 1700)
]

# Constraints for Bradley's availability
bradley_busy = [
    (day_map["Monday"], 930, 1100),
    (day_map["Monday"], 1130, 1200),
    (day_map["Monday"], 1230, 1300),
    (day_map["Monday"], 1400, 1500),
    (day_map["Tuesday"], 1030, 1100),
    (day_map["Tuesday"], 1200, 1300),
    (day_map["Tuesday"], 1330, 1400),
    (day_map["Tuesday"], 1530, 1630),
    (day_map["Wednesday"], 900, 1000),
    (day_map["Wednesday"], 1100, 1300),
    (day_map["Wednesday"], 1330, 1400),
    (day_map["Wednesday"], 1430, 1700),
    (day_map["Thursday"], 900, 1230),
    (day_map["Thursday"], 1330, 1400),
    (day_map["Thursday"], 1430, 1500),
    (day_map["Thursday"], 1530, 1630),
    (day_map["Friday"], 900, 930),
    (day_map["Friday"], 1000, 1230),
    (day_map["Friday"], 1300, 1330),
    (day_map["Friday"], 1400, 1430),
    (day_map["Friday"], 1530, 1630)
]

# Add constraints for Daniel's busy times
for d, s, e in daniel_busy:
    constraints.append(Or(day != d, Or(start_time >= e, start_time + 30 <= s)))

# Add constraints for Bradley's busy times
for d, s, e in bradley_busy:
    constraints.append(Or(day != d, Or(start_time >= e, start_time + 30 <= s)))

# Daniel does not want to meet on Wednesday or Thursday
constraints.append(day != day_map["Wednesday"])
constraints.append(day != day_map["Thursday"])

# Bradley does not want to meet on Monday, Tuesday before 12:00, or Friday
constraints.append(day != day_map["Monday"])
constraints.append(Or(day != day_map["Tuesday"], start_time >= 1200))
constraints.append(day != day_map["Friday"])

# Meeting must be within work hours and last 30 minutes
constraints.append(day >= 0)
constraints.append(day <= 4)
constraints.append(start_time >= 900)
constraints.append(start_time <= 1630)

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = days[model[day].as_long()]
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + 30
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start // 100:02}:{meeting_start % 100:02}\nEnd Time: {meeting_end // 100:02}:{meeting_end % 100:02}")
else:
    print("No solution found")