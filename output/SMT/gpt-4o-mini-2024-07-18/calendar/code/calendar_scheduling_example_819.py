from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for Ruth (in minutes from midnight)
busy_times = {
    "Monday": [(9 * 60, 17 * 60)],  # 9:00 - 17:00 (all day)
    "Tuesday": [(9 * 60, 17 * 60)], # 9:00 - 17:00 (all day)
    "Wednesday": [(9 * 60, 17 * 60)], # 9:00 - 17:00 (all day)
    "Thursday": [
        (9 * 60, 11 * 60),           # 9:00 - 11:00
        (11 * 60 + 30, 14 * 60 + 30), # 11:30 - 14:30
        (15 * 60, 17 * 60)            # 15:00 - 17:00
    ]
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting and the day
start_time = Int('start_time')
day = String('day')  # Variable for the meeting day (Monday, Tuesday, Wednesday, or Thursday)

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for Ruth based on the day
def add_busy_constraints(day):
    if day in busy_times:
        for busy_start, busy_end in busy_times[day]:
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on Monday, Tuesday, Wednesday, and Thursday
meeting_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
meeting_time_found = False

for meeting_day in meeting_days:
    # Clear existing constraints for the day variable
    solver.push()
    
    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints based on the current day
    add_busy_constraints(meeting_day)
    
    # Add Julie's preference: avoid meetings before 11:30 on Thursday
    if meeting_day == "Thursday":
        solver.add(start_time >= (11 * 60 + 30))  # 11:30 AM

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