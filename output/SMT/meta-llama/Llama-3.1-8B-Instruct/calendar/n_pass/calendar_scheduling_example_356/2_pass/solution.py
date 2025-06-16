from z3 import *

def schedule_meeting(day, start_time, end_time, existing_schedules, preferences):
    # Define the meeting duration
    meeting_duration = 30

    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    times = [Int(f"time_{i}") for i in range(96)]  # 96 possible time slots in a day

    # Add constraints for each participant
    for i, schedule in enumerate(existing_schedules):
        for j, time_slot in enumerate(schedule):
            if time_slot:
                # If a time slot is busy, add a constraint to the solver
                solver.add(times[j + time_slot[0]] >= time_slot[1])

    # Add constraints for the meeting time
    meeting_start = Int('meeting_start')
    meeting_end = meeting_start + meeting_duration
    solver.add(meeting_start >= 9 * 60)
    solver.add(meeting_start <= 17 * 60)
    solver.add(meeting_end >= meeting_start + meeting_duration)
    solver.add(meeting_end <= 17 * 60)

    # Add constraints for the day
    solver.add(meeting_start % (24 * 60) == 9 * 60)  # Meeting starts at 9:00

    # Add constraints for preferences
    for participant, pref in preferences.items():
        if pref and pref[0] == "before":
            solver.add(meeting_start >= pref[1])

    # Add constraints for each participant's schedule
    for i, schedule in enumerate(existing_schedules):
        for j, time_slot in enumerate(schedule):
            if time_slot:
                # If a time slot is busy, add a constraint to the solver
                solver.add(meeting_start + meeting_duration >= time_slot[1])

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        meeting_start = model[meeting_start].as_long()
        return f"SOLUTION:\nDay: {day}\nStart Time: {meeting_start // 60:02d}:{meeting_start % 60:02d}\nEnd Time: {(meeting_start + meeting_duration) // 60:02d}:{(meeting_start + meeting_duration) % 60:02d}"
    else:
        return "No solution exists"

# Existing schedules
existing_schedules = [
    [(12, 30), (13, 30)],  # Katherine
    [],  # Rebecca
    [(0, 30), (10, 30), (13, 30), (15, 30)],  # Julie
    [(0, 60), (10, 30), (11, 30), (14, 30), (15, 0)],  # Angela
    [(9, 30, 60), (11, 30, 90), (14, 0, 180), (16, 30, 210)],  # Nicholas
    [(0, 60), (11, 30, 90), (13, 0, 150), (15, 0, 180), (16, 30, 210)]  # Carl
]

# Preferences
preferences = {
    "Angela": ["before", 15 * 60]  # Angela prefers to avoid meetings before 15:00
}

# Solve the scheduling problem
print(schedule_meeting("Monday", 0, 0, existing_schedules, preferences))