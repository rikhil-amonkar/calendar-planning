from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_fishermans_wharf = 13  # Travel time from Pacific Heights to Fisherman's Wharf (in minutes)
travel_time_back = 12                   # Travel time from Fisherman's Wharf back to Pacific Heights (in minutes)

# Constants for timing
arrival_time = 9 * 60                  # Arrival at Pacific Heights at 9:00 AM (in minutes, 540)
betty_start = 8 * 60 + 45              # Betty will be at Fisherman's Wharf from 8:45 AM (525 minutes)
betty_end = 18 * 60                     # Betty leaves at 6:00 PM (1080 minutes)
min_meeting_duration = 105              # Minimum meeting duration (in minutes)

# Define variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_fishermans_wharf)  # Must arrive at Fisherman's Wharf after traveling
s.add(meeting_start >= betty_start)                                        # Meeting must start after Betty is available
s.add(meeting_start + min_meeting_duration <= betty_end)                  # Meeting must finish before Betty leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")