from z3 import *

# Define the variables for the day and time
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the duration of the meeting
meeting_duration_minutes = 30

# Define the available days as integers (Monday=0, Tuesday=1, Wednesday=2, Thursday=3)
days = {
    "Monday": 0,
    "Tuesday": 1,
    "Wednesday": 2,
    "Thursday": 3
}

# Constraints for Mary
mary_constraints = [
    Or(day != days["Tuesday"], Or(start_hour < 10, start_hour > 15, (start_hour == 10 and start_minute >= 30) or (start_hour == 15 and start_minute >= 30))),
    Or(day != days["Wednesday"], Or(start_hour < 9, start_hour > 15, (start_hour == 9 and start_minute >= 30) or (start_hour == 15 and start_minute >= 0))),
    Or(day != days["Thursday"], Or(start_hour < 9, start_hour > 11, (start_hour == 9 and start_minute >= 0) or (start_hour == 10 and start_minute >= 30) or (start_hour == 14 and start_minute >= 0) or (start_hour == 15 and start_minute >= 30)))
]

# Constraints for Alexis
alexis_constraints = [
    Or(day != days["Monday"], Or(start_hour < 9, start_hour > 12, (start_hour == 9 and start_minute >= 0) or (start_hour == 10 and start_minute >= 30) or (start_hour == 12 and start_minute >= 30))),
    Or(day != days["Tuesday"], Or(start_hour < 9, start_hour > 16, (start_hour == 9 and start_minute >= 0) or (start_hour == 10 and start_minute >= 30) or (start_hour == 12 and start_minute >= 0) or (start_hour == 15 and start_minute >= 30))),
    Or(day != days["Wednesday"], Or(start_hour < 9, start_hour > 11, (start_hour == 9 and start_minute >= 0) or (start_hour == 11 and start_minute >= 30))),
    Or(day != days["Thursday"], Or(start_hour < 10, start_hour > 16, (start_hour == 10 and start_minute >= 0) or (start_hour == 12 and start_minute >= 0) or (start_hour == 14 and start_minute >= 0) or (start_hour == 15 and start_minute >= 30) or (start_hour == 16 and start_minute >= 30)))
]

# Define the solver
solver = Solver()

# Add constraints for the day and time
solver.add(Or(day == days["Monday"], day == days["Tuesday"], day == days["Wednesday"], day == days["Thursday"]))
solver.add(And(start_hour >= 9, start_hour < 17))
solver.add(And(start_minute >= 0, start_minute < 60))

# Add constraints for the meeting duration
end_hour = If(start_minute + meeting_duration_minutes >= 60, start_hour + 1, start_hour)
end_minute = (start_minute + meeting_duration_minutes) % 60
solver.add(end_hour < 17)

# Ensure the start and end times do not fall within any unavailable periods
# Mary's constraints
solver.add(Or(day != days["Tuesday"], Or(start_hour < 10, start_hour > 15, (start_hour == 10 and start_minute >= 30) or (start_hour == 15 and start_minute >= 30))))
solver.add(Or(day != days["Tuesday"], Or(end_hour < 10, end_hour > 15, (end_hour == 10 and end_minute <= 30) or (end_hour == 15 and end_minute <= 30))))
solver.add(Or(day != days["Wednesday"], Or(start_hour < 9, start_hour > 15, (start_hour == 9 and start_minute >= 30) or (start_hour == 15 and start_minute >= 0))))
solver.add(Or(day != days["Wednesday"], Or(end_hour < 9, end_hour > 15, (end_hour == 9 and end_minute <= 30) or (end_hour == 15 and end_minute <= 0))))
solver.add(Or(day != days["Thursday"], Or(start_hour < 9, start_hour > 11, (start_hour == 9 and start_minute >= 0) or (start_hour == 10 and start_minute >= 30) or (start_hour == 14 and start_minute >= 0) or (start_hour == 15 and start_minute >= 30))))
solver.add(Or(day != days["Thursday"], Or(end_hour < 9, end_hour > 11, (end_hour == 9 and end_minute <= 0) or (end_hour == 10 and end_minute <= 30) or (end_hour == 14 and end_minute <= 0) or (end_hour == 15 and end_minute <= 30))))

# Alexis's constraints
solver.add(Or(day != days["Monday"], Or(start_hour < 9, start_hour > 12, (start_hour == 9 and start_minute >= 0) or (start_hour == 10 and start_minute >= 30) or (start_hour == 12 and start_minute >= 30))))
solver.add(Or(day != days["Monday"], Or(end_hour < 9, end_hour > 12, (end_hour == 9 and end_minute <= 0) or (end_hour == 10 and end_minute <= 30) or (end_hour == 12 and end_minute <= 30))))
solver.add(Or(day != days["Tuesday"], Or(start_hour < 9, start_hour > 16, (start_hour == 9 and start_minute >= 0) or (start_hour == 10 and start_minute >= 30) or (start_hour == 12 and start_minute >= 0) or (start_hour == 15 and start_minute >= 30))))
solver.add(Or(day != days["Tuesday"], Or(end_hour < 9, end_hour > 16, (end_hour == 9 and end_minute <= 0) or (end_hour == 10 and end_minute <= 30) or (end_hour == 12 and end_minute <= 0) or (end_hour == 15 and end_minute <= 30))))
solver.add(Or(day != days["Wednesday"], Or(start_hour < 9, start_hour > 11, (start_hour == 9 and start_minute >= 0) or (start_hour == 11 and start_minute >= 30))))
solver.add(Or(day != days["Wednesday"], Or(end_hour < 9, end_hour > 11, (end_hour == 9 and end_minute <= 0) or (end_hour == 11 and end_minute <= 30))))
solver.add(Or(day != days["Thursday"], Or(start_hour < 10, start_hour > 16, (start_hour == 10 and start_minute >= 0) or (start_hour == 12 and start_minute >= 0) or (start_hour == 14 and start_minute >= 0) or (start_hour == 15 and start_minute >= 30) or (start_hour == 16 and start_minute >= 30))))
solver.add(Or(day != days["Thursday"], Or(end_hour < 10, end_hour > 16, (end_hour == 10 and end_minute <= 0) or (end_hour == 12 and end_minute <= 0) or (end_hour == 14 and end_minute <= 0) or (end_hour == 15 and end_minute <= 30) or (end_hour == 16 and end_minute <= 30))))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = [k for k, v in days.items() if v == model[day].as_long()][0]
    meeting_start_hour = model[start_hour].as_long()
    meeting_start_minute = model[start_minute].as_long()
    meeting_end_hour = model[start_hour].as_long() + (model[start_minute].as_long() + meeting_duration_minutes) // 60
    meeting_end_minute = (model[start_minute].as_long() + meeting_duration_minutes) % 60
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")