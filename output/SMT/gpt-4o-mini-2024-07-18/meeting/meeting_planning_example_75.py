from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_fishermans_wharf = 13  # Travel time from Pacific Heights to Fisherman's Wharf (in minutes)
travel_time_back = 12                   # Travel time from Fisherman's Wharf back to Pacific Heights (in minutes)

# Constants for timing
arrival_time = 9 * 60                   # Arrival at Pacific Heights at 9:00 AM (540 minutes)
david_start = 11 * 60 + 30              # David will be at Fisherman's Wharf starting at 11:30 AM (690 minutes)
david_end = 14 * 60 + 45                # David leaves at 2:45 PM (885 minutes)
min_meeting_duration = 15                # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_fishermans_wharf)  # Must arrive at Fisherman's Wharf after traveling
s.add(meeting_start >= david_start)                                       # Meeting must start after David is available
s.add(meeting_start + min_meeting_duration <= david_end)                 # Meeting must finish before David leaves

# Ensure there is enough time to return after the meeting is over
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