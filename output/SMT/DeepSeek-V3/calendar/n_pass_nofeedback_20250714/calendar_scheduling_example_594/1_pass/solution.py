from z3 import *

def find_meeting_time(participants_busy_slots, duration_minutes, work_start, work_end):
    # Convert time strings to minutes since 9:00 (work_start)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return (hh - work_start_h) * 60 + mm
    
    work_start_h, work_start_m = map(int, work_start.split(':'))
    work_end_h, work_end_m = map(int, work_end.split(':'))
    work_start_total = 0  # Since we're measuring from work_start (9:00)
    work_end_total = (work_end_h - work_start_h) * 60 + work_end_m
    
    # Create a solver instance
    solver = Solver()
    
    # The meeting start time in minutes since work_start (0 to work_end_total - duration)
    meeting_start = Int('meeting_start')
    solver.add(meeting_start >= 0)
    solver.add(meeting_start <= work_end_total - duration_minutes)
    
    # The meeting should not overlap with any busy slot for any participant
    for participant_slots in participants_busy_slots:
        for slot in participant_slots:
            start, end = map(time_to_minutes, slot)
            solver.add(Or(
                meeting_start + duration_minutes <= start,
                meeting_start >= end
            ))
    
    # We want the earliest possible meeting time, so we find the minimal meeting_start
    solver.push()
    solver.check()
    model = solver.model()
    earliest_start = model[meeting_start].as_long()
    solver.pop()
    
    # Now, ensure that this is indeed the earliest by adding a constraint that meeting_start < earliest_start
    # and checking for unsat
    solver.add(meeting_start < earliest_start)
    if solver.check() == unsat:
        # No earlier time found, so earliest_start is correct
        pass
    else:
        # There's an earlier time, which shouldn't happen since we found the minimal
        pass
    
    # Convert back to HH:MM format
    total_minutes = earliest_start
    hh = work_start_h + (total_minutes // 60)
    mm = total_minutes % 60
    start_time = f"{hh:02d}:{mm:02d}"
    
    end_minutes = total_minutes + duration_minutes
    hh_end = work_start_h + (end_minutes // 60)
    mm_end = end_minutes % 60
    end_time = f"{hh_end:02d}:{mm_end:02d}"
    
    return start_time, end_time

# Define the problem
participants_busy_slots = [
    [("09:30", "10:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("16:30", "17:00")],  # Adam's busy slots
    [("10:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("16:30", "17:00")]   # Roy's busy slots
]
duration_minutes = 30
work_start = "09:00"
work_end = "17:00"

# Find the meeting time
start_time, end_time = find_meeting_time(participants_busy_slots, duration_minutes, work_start, work_end)

# Output the solution
print("SOLUTION:")
print(f"Day: Monday")
print(f"Start Time: {start_time}")
print(f"End Time: {end_time}")