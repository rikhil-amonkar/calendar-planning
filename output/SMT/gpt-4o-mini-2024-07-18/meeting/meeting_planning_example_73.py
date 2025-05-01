from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_pacific_heights = 7  # Travel time from Russian Hill to Pacific Heights (in minutes)
travel_time_back = 7                  # Travel time from Pacific Heights back to Russian Hill (in minutes)

# Constants for timings
arrival_time = 9 * 60                # Arrival at Russian Hill at 9:00 AM (540 minutes)
barbara_start = 7 * 60 + 15          # Barbara is at Pacific Heights from 7:15 AM (435 minutes)
barbara_end = 22 * 60                 # Barbara leaves at 10:00 PM (1200 minutes)
min_meeting_duration = 60             # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_pacific_heights)  # Must arrive at Pacific Heights after traveling
s.add(meeting_start >= barbara_start)                                   # Meeting must start after Barbara is available
s.add(meeting_start + min_meeting_duration <= barbara_end)             # Meeting must finish before Barbara leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")