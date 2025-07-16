from z3 import *

# Define the time slots in minutes from 9:00 to 17:00 (480 to 1020 minutes)
start_time = 480  # 9:00 AM
end_time = 1020   # 5:00 PM
meeting_duration = 30  # 30 minutes

# Create a list of time slots
time_slots = list(range(start_time, end_time - meeting_duration + 1))

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Define the constraints for each participant
constraints = [
    And(meeting_start >= start_time, meeting_start <= end_time - meeting_duration),
    Not(Or([And(meeting_start <= t, meeting_start + meeting_duration > t) for t in [570, 630]])),  # Joe's slots (9:30-10:00, 10:30-11:00)
    Not(Or([And(meeting_start <= t, meeting_start + meeting_duration > t) for t in [690, 900]])),  # Keith's slots (11:30-12:00, 15:00-15:30)
    Not(Or([And(meeting_start <= t, meeting_start + meeting_duration > t) for t in [540, 780]])),  # Patricia's slots (9:00-9:30, 13:00-13:30)
    Not(Or([And(meeting_start <= t, meeting_start + meeting_duration > t) for t in [540, 690, 990]])),  # Nancy's slots (9:00-11:00, 11:30-16:30)
    Not(Or([And(meeting_start <= t, meeting_start + meeting_duration > t) for t in [540, 630, 690, 780, 870, 930, 990]]))  # Pamela's slots (9:00-10:00, 10:30-11:00, 11:30-12:30, 13:00-14:00, 14:30-15:00, 15:30-16:00, 16:30-17:00)
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_value = model[meeting_start].as_long()
    meeting_end_value = meeting_start_value + meeting_duration
    
    # Convert the times back to HH:MM format
    def convert_to_hhmm(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    meeting_start_hhmm = convert_to_hhmm(meeting_start_value)
    meeting_end_hhmm = convert_to_hhmm(meeting_end_value)
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_hhmm}\nEnd Time: {meeting_end_hhmm}")
else:
    print("No solution found")