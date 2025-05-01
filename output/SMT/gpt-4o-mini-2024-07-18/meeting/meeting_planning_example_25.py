from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times and other timing
arrival_time = 9 * 60  # Arrival at Golden Gate Park at 9:00 AM (in minutes, 540)
travel_time_to_chinatown = 23  # Travel time from Golden Gate Park to Chinatown (in minutes)
travel_time_back = 23           # Travel time from Chinatown back to Golden Gate Park (in minutes)

# David's availability
david_start = 16 * 60        # David is at Chinatown starting at 4:00 PM (960 minutes)
david_end = 21 * 60 + 45     # David leaves at 9:45 PM (1305 minutes)
min_meeting_duration = 105    # Minimum meeting duration in minutes

# Define variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_chinatown)  # Must arrive at Chinatown after traveling
s.add(meeting_start >= david_start)                              # Meeting must start after David is available
s.add(meeting_start + min_meeting_duration <= david_end)        # Meeting must finish before David leaves

# Add a constraint to ensure there's enough time to return after the meeting
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