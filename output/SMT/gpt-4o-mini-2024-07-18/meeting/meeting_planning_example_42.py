from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times and other timing
travel_time_to_presidio = 17  # Travel time from Nob Hill to Presidio (in minutes)
travel_time_back = 18          # Travel time from Presidio back to Nob Hill (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Nob Hill at 9:00 AM (540 minutes)
timothy_start = 13 * 60        # Timothy is at Presidio starting at 1:00 PM (780 minutes)
timothy_end = 19 * 60          # Timothy leaves at 7:00 PM (1140 minutes)
min_meeting_duration = 30       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_presidio)  # Must arrive at Presidio after traveling
s.add(meeting_start >= timothy_start)                           # Meeting must start after Timothy is available
s.add(meeting_start + min_meeting_duration <= timothy_end)      # Meeting must finish before Timothy leaves

# Ensure there is enough time to return to Nob Hill after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format the time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format the time to HH:MM
else:
    print("No possible trip plan found.")