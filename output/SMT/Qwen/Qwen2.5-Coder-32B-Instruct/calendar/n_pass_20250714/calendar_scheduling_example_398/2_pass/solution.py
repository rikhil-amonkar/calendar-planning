from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 AM
end_time = 17 * 60   # 5:00 PM
meeting_duration = 30  # 30 minutes

# Create a Z3 solver instance
solver = Solver()

# Define variables for the start time of the meeting
meeting_start = Int('meeting_start')

# Add constraints for the meeting start time to be within working hours
solver.add(meeting_start >= start_time)
solver.add(meeting_start <= end_time - meeting_duration)

# Define the availability of each participant
doris_unavailable = Or(
    And(meeting_start >= 9 * 60, meeting_start + meeting_duration <= 11 * 60),
    And(meeting_start >= 13 * 60 + 30, meeting_start + meeting_duration <= 14 * 60),
    And(meeting_start >= 16 * 60, meeting_start + meeting_duration <= 16 * 60 + 30)
)

theresa_unavailable = Or(
    And(meeting_start >= 10 * 60, meeting_start + meeting_duration <= 12 * 60)
)

christian_unavailable = False  # Christian is available all day

terry_unavailable = Or(
    And(meeting_start >= 9 * 60 + 30, meeting_start + meeting_duration <= 10 * 60),
    And(meeting_start >= 11 * 60 + 30, meeting_start + meeting_duration <= 12 * 60),
    And(meeting_start >= 12 * 60 + 30, meeting_start + meeting_duration <= 13 * 60),
    And(meeting_start >= 13 * 60 + 30, meeting_start + meeting_duration <= 14 * 60),
    And(meeting_start >= 14 * 60 + 30, meeting_start + meeting_duration <= 15 * 60),
    And(meeting_start >= 15 * 60 + 30, meeting_start + meeting_duration <= 17 * 60)
)

carolyn_unavailable = Or(
    And(meeting_start >= 9 * 60, meeting_start + meeting_duration <= 10 * 60 + 30),
    And(meeting_start >= 11 * 60, meeting_start + meeting_duration <= 11 * 60 + 30),
    And(meeting_start >= 12 * 60, meeting_start + meeting_duration <= 13 * 60),
    And(meeting_start >= 13 * 60 + 30, meeting_start + meeting_duration <= 14 * 60 + 30),
    And(meeting_start >= 15 * 60, meeting_start + meeting_duration <= 17 * 60)
)

kyle_unavailable = Or(
    And(meeting_start >= 9 * 60, meeting_start + meeting_duration <= 9 * 60 + 30),
    And(meeting_start >= 11 * 60 + 30, meeting_start + meeting_duration <= 12 * 60),
    And(meeting_start >= 12 * 60 + 30, meeting_start + meeting_duration <= 13 * 60),
    And(meeting_start >= 14 * 60 + 30, meeting_start + meeting_duration <= 17 * 60)
)

# Add constraints to ensure the meeting does not overlap with any unavailable times
solver.add(Not(doris_unavailable))
solver.add(Not(theresa_unavailable))
solver.add(Not(christian_unavailable))
solver.add(Not(terry_unavailable))
solver.add(Not(carolyn_unavailable))
solver.add(Not(kyle_unavailable))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_hour = meeting_start_minutes // 60
    meeting_start_minute = meeting_start_minutes % 60
    meeting_end_minutes = meeting_start_minutes + meeting_duration
    meeting_end_hour = meeting_end_minutes // 60
    meeting_end_minute = meeting_end_minutes % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found.")