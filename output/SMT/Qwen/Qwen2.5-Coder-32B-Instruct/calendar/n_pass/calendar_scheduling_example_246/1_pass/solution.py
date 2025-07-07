from z3 import *

# Define the time intervals in minutes since 9:00 AM
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Meeting duration in minutes
meeting_duration = 30

# Define the available time slots for each person
jacob_busy = [(time_to_minutes("13:30"), time_to_minutes("14:00")), (time_to_minutes("14:30"), time_to_minutes("15:00"))]
diana_busy = [(time_to_minutes("9:30"), time_to_minutes("10:00")), (time_to_minutes("11:30"), time_to_minutes("12:00")),
              (time_to_minutes("13:00"), time_to_minutes("13:30")), (time_to_minutes("16:00"), time_to_minutes("16:30"))]
adam_busy = [(time_to_minutes("9:30"), time_to_minutes("10:30")), (time_to_minutes("11:00"), time_to_minutes("12:30")),
             (time_to_minutes("15:30"), time_to_minutes("16:00"))]
angela_busy = [(time_to_minutes("9:30"), time_to_minutes("10:00")), (time_to_minutes("10:30"), time_to_minutes("12:00")),
               (time_to_minutes("13:00"), time_to_minutes("15:30")), (time_to_minutes("16:00"), time_to_minutes("16:30"))]
dennis_busy = [(time_to_minutes("9:00"), time_to_minutes("9:30")), (time_to_minutes("10:30"), time_to_minutes("11:30")),
               (time_to_minutes("13:00"), time_to_minutes("15:00")), (time_to_minutes("16:30"), time_to_minutes("17:00"))]

# Define the solver
s = Solver()

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Add constraints for each person's availability
for busy in jacob_busy:
    s.add(Or(meeting_start >= busy[1], meeting_start + meeting_duration <= busy[0]))

for busy in diana_busy:
    s.add(Or(meeting_start >= busy[1], meeting_start + meeting_duration <= busy[0]))

for busy in adam_busy:
    s.add(Or(meeting_start >= busy[1], meeting_start + meeting_duration <= busy[0]))

for busy in angela_busy:
    s.add(Or(meeting_start >= busy[1], meeting_start + meeting_duration <= busy[0]))

for busy in dennis_busy:
    s.add(Or(meeting_start >= busy[1], meeting_start + meeting_duration <= busy[0]))

# Ensure the meeting is within work hours (9:00 to 17:00)
s.add(meeting_start >= 0)
s.add(meeting_start + meeting_duration <= time_to_minutes("17:00"))

# Check if there is a solution
if s.check() == sat:
    model = s.model()
    start_time_minutes = model[meeting_start].as_long()
    end_time_minutes = start_time_minutes + meeting_duration
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {minutes_to_time(start_time_minutes)}")
    print(f"End Time: {minutes_to_time(end_time_minutes)}")
else:
    print("No solution found")