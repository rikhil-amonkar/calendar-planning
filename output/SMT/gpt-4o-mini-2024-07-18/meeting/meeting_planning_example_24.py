from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_presidio = 17  # Time from Nob Hill to Presidio (in minutes)
travel_time_back = 18          # Time from Presidio back to Nob Hill (in minutes)

# Constants for timing
arrival_time = 9 * 60  # Arrival time at Nob Hill (9:00 AM in minutes)
matthew_start = 11 * 60  # Matthew starts being at Presidio at 11:00 AM (660 minutes)
matthew_end = 15 * 60 + 15  # Matthew is there until 3:15 PM (915 minutes)
min_meeting_duration = 30  # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_presidio)  # Must arrive at Presidio after traveling
s.add(meeting_start >= matthew_start)                            # Meeting must start after Matthew is available
s.add(meeting_start + min_meeting_duration <= matthew_end)      # Meeting must finish before Matthew leaves

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