from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_russian_hill = 4  # Travel time from North Beach to Russian Hill (in minutes)
travel_time_back = 5               # Travel time from Russian Hill back to North Beach (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at North Beach at 9:00 AM (540 minutes)
william_start = 13 * 60 + 15       # William will be at Russian Hill from 1:15 PM (795 minutes)
william_end = 21 * 60 + 30         # William leaves at 9:30 PM (1290 minutes)
min_meeting_duration = 15           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_russian_hill)  # Must arrive at Russian Hill after traveling
s.add(meeting_start >= william_start)                                 # Meeting must start after William is available
s.add(meeting_start + min_meeting_duration <= william_end)           # Meeting must finish before William leaves

# Ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")