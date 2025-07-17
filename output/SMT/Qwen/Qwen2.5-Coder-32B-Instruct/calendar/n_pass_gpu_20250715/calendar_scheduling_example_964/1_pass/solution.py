from z3 import *

# Define the possible days and times
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
start_times = [time for time in range(9, 17) for minute in [0, 30]]
end_times = [time for time in range(9, 18) for minute in [0, 30]]

# Create a solver instance
solver = Solver()

# Define variables for the meeting day and time
meeting_day = Int('meeting_day')
meeting_start_time = Int('meeting_start_time')
meeting_end_time = Int('meeting_end_time')

# Add constraints for the meeting duration
solver.add(meeting_end_time == meeting_start_time + 2)  # 1 hour meeting

# Map days to integers
day_map = {day: i for i, day in enumerate(days)}

# Add constraints for each person's availability
# Betty's schedule
betty_unavailable = [
    (day_map["Monday"], 20), (day_map["Monday"], 21),  # 10:00 to 10:30
    (day_map["Monday"], 23), (day_map["Monday"], 24), (day_map["Monday"], 25),  # 11:30 to 12:30
    (day_map["Monday"], 32), (day_map["Monday"], 33),  # 16:00 to 16:30
    (day_map["Tuesday"], 19), (day_map["Tuesday"], 20),  # 9:30 to 10:00
    (day_map["Tuesday"], 21), (day_map["Tuesday"], 22),  # 10:30 to 11:00
    (day_map["Tuesday"], 24), (day_map["Tuesday"], 25),  # 12:00 to 12:30
    (day_map["Tuesday"], 27), (day_map["Tuesday"], 28), (day_map["Tuesday"], 29),  # 13:30 to 15:00
    (day_map["Tuesday"], 33), (day_map["Tuesday"], 34),  # 16:30 to 17:00
    (day_map["Wednesday"], 27), (day_map["Wednesday"], 28),  # 13:30 to 14:00
    (day_map["Wednesday"], 29), (day_map["Wednesday"], 30),  # 14:30 to 15:00
    (day_map["Friday"], 18), (day_map["Friday"], 19),  # 9:00 to 10:00
    (day_map["Friday"], 23), (day_map["Friday"], 24),  # 11:30 to 12:00
    (day_map["Friday"], 25), (day_map["Friday"], 26),  # 12:30 to 13:00
    (day_map["Friday"], 29), (day_map["Friday"], 30),  # 14:30 to 15:00
]

# Megan's schedule
megan_unavailable = [
    (day_map["Monday"], 18), (day_map["Monday"], 19), (day_map["Monday"], 20), (day_map["Monday"], 21), (day_map["Monday"], 22), (day_map["Monday"], 23), (day_map["Monday"], 24), (day_map["Monday"], 25), (day_map["Monday"], 26), (day_map["Monday"], 27), (day_map["Monday"], 28), (day_map["Monday"], 29), (day_map["Monday"], 30), (day_map["Monday"], 31), (day_map["Monday"], 32), (day_map["Monday"], 33), (day_map["Monday"], 34),  # 9:00 to 17:00
    (day_map["Tuesday"], 18), (day_map["Tuesday"], 19),  # 9:00 to 9:30
    (day_map["Tuesday"], 20), (day_map["Tuesday"], 21),  # 10:00 to 10:30
    (day_map["Tuesday"], 24), (day_map["Tuesday"], 25), (day_map["Tuesday"], 26), (day_map["Tuesday"], 27),  # 12:00 to 14:00
    (day_map["Tuesday"], 30), (day_map["Tuesday"], 31),  # 15:00 to 15:30
    (day_map["Tuesday"], 32), (day_map["Tuesday"], 33),  # 16:00 to 16:30
    (day_map["Wednesday"], 19), (day_map["Wednesday"], 20),  # 9:30 to 10:30
    (day_map["Wednesday"], 22), (day_map["Wednesday"], 23),  # 11:00 to 11:30
    (day_map["Wednesday"], 26), (day_map["Wednesday"], 27),  # 12:30 to 13:00
    (day_map["Wednesday"], 28), (day_map["Wednesday"], 29),  # 13:30 to 14:30
    (day_map["Wednesday"], 31), (day_map["Wednesday"], 32), (day_map["Wednesday"], 33), (day_map["Wednesday"], 34),  # 15:30 to 17:00
    (day_map["Thursday"], 19), (day_map["Thursday"], 20),  # 9:00 to 10:30
    (day_map["Thursday"], 23), (day_map["Thursday"], 24), (day_map["Thursday"], 25), (day_map["Thursday"], 26),  # 11:30 to 14:00
    (day_map["Thursday"], 28), (day_map["Thursday"], 29),  # 14:30 to 15:00
    (day_map["Thursday"], 31), (day_map["Thursday"], 32),  # 15:30 to 16:30
    (day_map["Friday"], 18), (day_map["Friday"], 19), (day_map["Friday"], 20), (day_map["Friday"], 21), (day_map["Friday"], 22), (day_map["Friday"], 23), (day_map["Friday"], 24), (day_map["Friday"], 25), (day_map["Friday"], 26), (day_map["Friday"], 27), (day_map["Friday"], 28), (day_map["Friday"], 29), (day_map["Friday"], 30), (day_map["Friday"], 31), (day_map["Friday"], 32), (day_map["Friday"], 33), (day_map["Friday"], 34),  # 9:00 to 17:00
]

# Add constraints to ensure the meeting does not overlap with unavailable times
for day, time in betty_unavailable:
    solver.add(Or(meeting_day != day, Or(meeting_start_time >= time + 2, meeting_end_time <= time)))

for day, time in megan_unavailable:
    solver.add(Or(meeting_day != day, Or(meeting_start_time >= time + 2, meeting_end_time <= time)))

# Betty cannot meet on Wednesday
solver.add(meeting_day != day_map["Wednesday"])

# Betty cannot meet on Thursday
solver.add(meeting_day != day_map["Thursday"])

# Ensure the meeting is within working hours
solver.add(meeting_day >= 0)
solver.add(meeting_day <= len(days) - 1)
solver.add(meeting_start_time >= 18)  # 9:00
solver.add(meeting_start_time <= 34)  # 17:00
solver.add(meeting_end_time <= 36)  # 18:00

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day = days[model[meeting_day].as_long()]
    start_time = start_times[model[meeting_start_time].as_long()]
    end_time = end_times[model[meeting_end_time].as_long()]

    start_hour = start_time // 2
    start_minute = (start_time % 2) * 30
    end_hour = end_time // 2
    end_minute = (end_time % 2) * 30

    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")