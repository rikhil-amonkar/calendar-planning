from z3 import *

# Define the time slots as integers representing minutes since 9:00 AM
def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return (hours - 9) * 60 + minutes

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Meeting duration in minutes
meeting_duration = 30

# Define the variables for the start time of the meeting
start_time = Int('start_time')

# Define the constraints
constraints = [
    # Meeting must be within work hours (9:00 to 17:00)
    start_time >= 0,
    start_time + meeting_duration <= time_to_minutes('17:00'),  # 17:00 - 9:00 = 8 hours = 480 minutes
    
    # Emily's constraints
    Or(start_time + meeting_duration <= time_to_minutes('10:00'),
       start_time >= time_to_minutes('10:30')),
    Or(start_time + meeting_duration <= time_to_minutes('16:00'),
       start_time >= time_to_minutes('16:30')),
    
    # Maria's constraints
    Or(start_time + meeting_duration <= time_to_minutes('10:30'),
       start_time >= time_to_minutes('11:00')),
    Or(start_time + meeting_duration <= time_to_minutes('14:00'),
       start_time >= time_to_minutes('14:30')),
    
    # Carl's constraints
    Or(start_time + meeting_duration <= time_to_minutes('09:30'),
       start_time >= time_to_minutes('12:30')),
    Or(start_time + meeting_duration <= time_to_minutes('13:30'),
       start_time >= time_to_minutes('15:30')),
    
    # David's constraints
    Or(start_time + meeting_duration <= time_to_minutes('09:30'),
       start_time >= time_to_minutes('11:00')),
    Or(start_time + meeting_duration <= time_to_minutes('11:30'),
       start_time >= time_to_minutes('12:00')),
    Or(start_time + meeting_duration <= time_to_minutes('12:30'),
       start_time >= time_to_minutes('13:30')),
    Or(start_time + meeting_duration <= time_to_minutes('14:00'),
       start_time >= time_to_minutes('15:00')),
    
    # Frank's constraints
    Or(start_time + meeting_duration <= time_to_minutes('09:30'),
       start_time >= time_to_minutes('11:30')),
    Or(start_time + meeting_duration <= time_to_minutes('12:30'),
       start_time >= time_to_minutes('13:30')),
]

# Create a solver instance
solver = Solver()

# Add constraints to the solver
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_minutes = model[start_time].as_long()
    start_time_str = minutes_to_time(start_minutes)
    end_time_str = minutes_to_time(start_minutes + meeting_duration)
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")