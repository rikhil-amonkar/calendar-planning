from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_presidio = 11  # Travel time from Golden Gate Park to Presidio (in minutes)
travel_time_back = 12          # Travel time from Presidio back to Golden Gate Park (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Golden Gate Park at 9:00 AM (in minutes, 540)
stephanie_start = 19 * 60 + 15  # Stephanie will be at Presidio from 7:15 PM (in minutes, 1155)
stephanie_end = 22 * 60         # Stephanie leaves at 10:00 PM (in minutes, 1320)
min_meeting_duration = 90       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_presidio)  # Must arrive at Presidio after traveling
s.add(meeting_start >= stephanie_start)                          # Meeting must start after Stephanie is available
s.add(meeting_start + min_meeting_duration <= stephanie_end)    # Meeting must finish before Stephanie leaves

# Add a constraint to ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")