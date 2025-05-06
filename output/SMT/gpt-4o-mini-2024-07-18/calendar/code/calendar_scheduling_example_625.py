from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing busy times for Harold (in minutes from midnight)
harold_busy = {
    "Monday": [
        (9 * 60, 10 * 60),   # 9:00 - 10:00
        (10 * 60 + 30, 17 * 60)  # 10:30 - 17:00
    ],
    "Tuesday": [
        (9 * 60, 9 * 60 + 30),  # 9:00 - 9:30
        (10 * 60 + 30, 11 * 60),  # 10:30 - 11:30
        (12 * 60 + 30, 13 * 60 + 30),  # 12:30 - 13:30
        (14 * 60 + 30, 15 * 60 + 30),  # 14:30 - 15:30
        (16 * 60, 17 * 60)  # 16:00 - 17:00
    ]
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')
day = String('day')

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for Harold according to the day
def add_harold_constraints(day):
    if day == "Monday":
        for busy_start, busy_end in harold_busy['Monday']:
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))
        # Avoid more meetings on Monday (can have a meeting only in the available time)
    elif day == "Tuesday":
        for busy_start, busy_end in harold_busy['Tuesday']:
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))
        # Constraint to avoid meeting before 14:30 on Tuesday
        solver.add(start_time >= 14 * 60 + 30)

# Checking on both Monday and Tuesday
meeting_time_found = False

for meeting_day in ["Monday", "Tuesday"]:
    # Clear existing constraints for the day variable
    solver.push()
    # Assign the current day for the meeting
    solver.add(day == meeting_day)
    
    # Add Harold's constraints based on the day
    add_harold_constraints(meeting_day)

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start_time].as_long()
        meeting_end = meeting_start + meeting_duration
        print(f"Meeting can be scheduled on {meeting_day} from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
        meeting_time_found = True
        break
        
    # Pop the last constraints to check the next day
    solver.pop()

if not meeting_time_found:
    print("No available time found for the meeting.")