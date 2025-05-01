from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_pacific_heights = 8  # Travel time from Nob Hill to Pacific Heights (in minutes)
travel_time_back = 8                  # Travel time from Pacific Heights back to Nob Hill (in minutes)

# Constants for timing
arrival_time = 9 * 60                       # Arrival at Nob Hill at 9:00 AM (540 minutes)
margaret_start = 15 * 60 + 45                # Margaret will be at Pacific Heights from 3:45 PM (945 minutes)
margaret_end = 19 * 60 + 15                  # Margaret leaves at 7:15 PM (1115 minutes)
min_meeting_duration = 45                     # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_pacific_heights)  # Must arrive at Pacific Heights after traveling
s.add(meeting_start >= margaret_start)                                   # Meeting must start after Margaret is available
s.add(meeting_start + min_meeting_duration <= margaret_end)             # Meeting must finish before Margaret leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")