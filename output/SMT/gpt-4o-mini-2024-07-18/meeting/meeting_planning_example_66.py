from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_presidio = 17  # Travel time from Nob Hill to Presidio (in minutes)
travel_time_back = 18          # Travel time from Presidio back to Nob Hill (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Nob Hill at 9:00 AM (540 minutes)
robert_start = 11 * 60 + 15    # Robert will be at Presidio from 11:15 AM (675 minutes)
robert_end = 17 * 60 + 45      # Robert leaves at 5:45 PM (1065 minutes)
min_meeting_duration = 120       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_presidio)  # Must arrive at Presidio after traveling
s.add(meeting_start >= robert_start)                            # Meeting must start after Robert is available
s.add(meeting_start + min_meeting_duration <= robert_end)      # Meeting must finish before Robert leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when the meeting ends

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")