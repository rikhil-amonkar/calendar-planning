from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for Nancy (in minutes from midnight)
nancy_busy = {
    "Monday": [
        (10 * 60, 10 * 60 + 30),  # 10:00 - 10:30
        (11 * 60 + 30, 12 * 60 + 30),  # 11:30 - 12:30
        (13 * 60 + 30, 14 * 60),  # 1:30 - 2:00
        (14 * 60 + 30, 15 * 60 + 30),  # 2:30 - 3:30
        (16 * 60, 17 * 60)  # 4:00 - 5:00
    ],
    "Tuesday": [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30 - 10:30
        (11 * 60, 11 * 60 + 30),  # 11:00 - 11:30
        (12 * 60, 12 * 60 + 30),  # 12:00 - 12:30
        (13 * 60, 13 * 60 + 30),  # 1:00 - 1:30
        (15 * 60 + 30, 16 * 60)  # 3:30 - 4:00
    ],
    "Wednesday": [
        (10 * 60, 11 * 60 + 30),  # 10:00 - 11:30
        (13 * 60 + 30, 16 * 60)  # 1:30 - 4:00
    ]
}

# Define busy times for Jose (in minutes from midnight)
jose_busy = {
    "Monday": [
        (9 * 60, 17 * 60)  # All day
    ],
    "Tuesday": [
        (9 * 60, 17 * 60)  # All day
    ],
    "Wednesday": [
        (9 * 60, 9 * 60 + 30),  # 9:00 - 9:30
        (10 * 60, 12 * 60 + 30),  # 10:00 - 12:30
        (13 * 60 + 30, 14 * 60 + 30),  # 1:30 - 2:30
        (15 * 60, 17 * 60)  # 3:00 - 5:00
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

# Function to add busy time constraints
def add_busy_constraints(day):
    nancy_times = nancy_busy[day]
    jose_times = jose_busy[day]
    
    # Add constraints for Nancy
    for busy_start, busy_end in nancy_times:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))
        
    # Add constraints for Jose
    for busy_start, busy_end in jose_times:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check on Monday, Tuesday, and Wednesday for the earliest availability
days = ["Monday", "Tuesday", "Wednesday"]
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