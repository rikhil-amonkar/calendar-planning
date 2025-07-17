from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the participants
participants = ['Tyler', 'Kelly', 'Stephanie', 'Hannah', 'Joe', 'Diana', 'Deborah']

# Define the constraints for each participant
constraints = {
    'Stephanie': [(1100, 1130), (1430, 1500)],
    'Joe': [(900, 930), (1000, 1200), (1230, 1300), (1400, 1700)],
    'Diana': [(900, 1030), (1130, 1200), (1300, 1400), (1430, 1530), (1600, 1700)],
    'Deborah': [(900, 1000), (1030, 1200), (1230, 1300), (1330, 1400), (1430, 1530), (1600, 1630)]
}

# Create a Z3 solver
solver = Solver()

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Add constraints for the meeting duration (30 minutes) and the work hours (9:00 to 17:00)
solver.add(start_time >= 900)
solver.add(start_time <= 1630)  # 1630 to allow for a 30-minute meeting ending at 17:00

# Add constraints for each participant's availability
for participant in participants:
    if participant in constraints:
        for busy_start, busy_end in constraints[participant]:
            solver.add(Or(start_time < busy_start, start_time + 30 > busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    start_hour = start // 100
    start_minute = start % 100
    end_hour = end // 100
    end_minute = end % 100
    # Ensure minutes are within 0-59
    if end_minute >= 60:
        end_hour += 1
        end_minute -= 60
    start_time_str = f"{start_hour:02}:{start_minute:02}"
    end_time_str = f"{end_hour:02}:{end_minute:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")