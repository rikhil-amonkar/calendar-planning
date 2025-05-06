from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing busy times for each participant (in minutes from midnight)
busy_times = {
    "Tyler": {
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),   # 9:00 - 9:30
            (14 * 60 + 30, 15 * 60)  # 2:30 - 3:00
        ],
        "Wednesday": [
            (10 * 60 + 30, 11 * 60),  # 10:30 - 11:00
            (12 * 60 + 30, 13 * 60),   # 12:30 - 1:00
            (13 * 60 + 30, 14 * 60),   # 1:30 - 2:00
            (16 * 60 + 30, 17 * 60)     # 4:30 - 5:00
        ]
    },
    "Ruth": {
        "Monday": [
            (9 * 60, 10 * 60),          # 9:00 - 10:00
            (10 * 60 + 30, 12 * 60),    # 10:30 - 12:00
            (12 * 60 + 30, 14 * 60 + 30), # 12:30 - 2:30
            (15 * 60, 16 * 60),         # 3:00 - 4:00
            (16 * 60 + 30, 17 * 60)     # 4:30 - 5:00
        ],
        "Tuesday": [
            (9 * 60, 17 * 60)           # 9:00 - 5:00
        ],
        "Wednesday": [
            (9 * 60, 17 * 60)           # 9:00 - 5:00
        ]
    }
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting and the day
start_time = Int('start_time')
day = String('day')  # Variable for the meeting day (Monday, Tuesday, or Wednesday)

# Constraints: meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for each participant based on the day
def add_busy_constraints(participant, day):
    if day in busy_times[participant]:
        for busy_start, busy_end in busy_times[participant][day]:
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check available times on Monday, Tuesday, and Wednesday
days = ["Monday", "Tuesday", "Wednesday"]
meeting_time_found = False

for meeting_day in days:
    # Clear existing constraints for the day variable
    solver.push()
    
    # Assign the current day for the meeting
    solver.add(day == meeting_day)

    # Add busy constraints based on the current day
    add_busy_constraints("Tyler", meeting_day)
    add_busy_constraints("Ruth", meeting_day)
    
    # Add Tyler's preference: avoid meetings before 16:00 on Monday
    if meeting_day == "Monday":
        solver.add(start_time >= (16 * 60))  # 16:00

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