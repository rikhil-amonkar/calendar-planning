from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_russian_hill = 23  # Travel time from Bayview to Russian Hill (in minutes)
travel_time_back = 23               # Travel time from Russian Hill back to Bayview (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Bayview at 9:00 AM (in minutes, 540)
john_start = 17 * 60 + 30          # John is at Russian Hill starting at 5:30 PM (in minutes, 1050)
john_end = 21 * 60                  # John leaves at 9:00 PM (in minutes, 1260)
min_meeting_duration = 75           # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_russian_hill)  # Must arrive at Russian Hill after traveling
s.add(meeting_start >= john_start)                                   # Meeting must start after John is available
s.add(meeting_start + min_meeting_duration <= john_end)             # Meeting must finish before John leaves

# Add constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")