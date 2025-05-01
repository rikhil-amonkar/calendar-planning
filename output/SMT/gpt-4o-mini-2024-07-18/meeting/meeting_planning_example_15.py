from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for timing and travel
arrival_time = 9 * 60  # Arrival at Russian Hill at 9:00 AM (in minutes from midnight)
travel_time_to_golden_gate = 21  # Travel time from Russian Hill to Golden Gate Park (in minutes)
travel_time_back = 19              # Travel time from Golden Gate Park back to Russian Hill (in minutes)

# John's availability
john_start = 13 * 60              # John is at Golden Gate Park starting at 1:00 PM (780 minutes)
john_end = 18 * 60 + 15           # John leaves at 6:15 PM (1095 minutes)
min_meeting_duration = 90          # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_golden_gate)  # Must arrive at Golden Gate Park after traveling
s.add(meeting_start >= john_start)                                  # Meeting must start after John is available
s.add(meeting_start + min_meeting_duration <= john_end)            # Meeting must finish before John leaves

# Add a constraint to ensure you have enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")