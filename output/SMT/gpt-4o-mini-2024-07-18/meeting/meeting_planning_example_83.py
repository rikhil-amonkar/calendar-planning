from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_golden_gate = 12  # Travel time from Presidio to Golden Gate Park (in minutes)
travel_time_back = 11              # Travel time from Golden Gate Park back to Presidio (in minutes)

# Constants for arrival and availability
arrival_time = 9 * 60              # Arrival time at Presidio (9:00 AM in minutes)
carol_start = 21 * 60 + 45         # Carol will be at Golden Gate Park starting at 9:45 PM (1305 minutes)
carol_end = 22 * 60 + 30           # Carol leaves at 10:30 PM (1350 minutes)
min_meeting_duration = 45           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_golden_gate)  # Must arrive at Golden Gate Park after traveling
s.add(meeting_start >= carol_start)                                  # Meeting must start after Carol is available
s.add(meeting_start + min_meeting_duration <= carol_end)            # Meeting must finish before Carol leaves

# Ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")