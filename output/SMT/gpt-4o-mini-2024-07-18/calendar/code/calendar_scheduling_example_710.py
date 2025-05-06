from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for Cheryl (in minutes from midnight)
cheryl_busy = {
    "Monday": [
        (9 * 60, 9 * 60 + 30),  # 9:00 - 9:30
        (11 * 60 + 30, 13 * 60),  # 11:30 - 1:00
        (15 * 60 + 30, 16 * 60)  # 3:30 - 4:00
    ],
    "Tuesday": [
        (15 * 60, 15 * 60 + 30)   # 3:00 - 3:30
    ],
    "Wednesday": []  # Cheryl can't meet on Wednesday
}

# Define busy times for Kyle (in minutes from midnight)
kyle_busy = {
    "Monday": [
        (9 * 60, 17 * 60)  # All day
    ],
    "Tuesday": [
        (9 * 60 + 30, 17 * 60)  # 9:30 - 5:00
    ],
    "Wednesday": [
        (9 * 60, 9 * 60 + 30),  # 9:00 - 9:30
        (10 * 60, 13 * 60),      # 10:00 - 1:00
        (13 * 60 + 30, 14 * 60),  # 1:30 - 2:00
        (14 * 60 + 30, 17 * 60)   # 2:30 - 5:00
    ]
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting and a string for the day
start_time = Int('start_time')
day = String('day')

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for both Cheryl and Kyle depending on the day
def add_busy_constraints(day):
    cheryl_times = cheryl_busy[day]
    kyle_times = kyle_busy[day]
    
    # Add constraints for Cheryl
    for busy_start, busy_end in cheryl_times:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))
        
    # Add constraints for Kyle
    for busy_start, busy_end in kyle_times:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check on Monday and Tuesday for the earliest availability
days = ["Monday", "Tuesday"]
meeting_time_found = False

for meeting_day in days:
    # Clear existing constraints for the day variable
    solver.push()
    # Assign the current day for the meeting
    solver.add(day == meeting_day)
    
    # Add busy constraints based on the current day
    add_busy_constraints(meeting_day)

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start_time].as_long()
        meeting_end = meeting_start + meeting_duration
        print(f"Meeting can be scheduled on {meeting_day} from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
        meeting_time_found = True
        break  # Exit the loop upon finding the earliest meeting time
        
    # Pop the last constraints to check the next day
    solver.pop()

if not meeting_time_found:
    print("No available time found for the meeting.")