from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_alamo = 10  # Travel time from Golden Gate Park to Alamo Square (in minutes)
travel_time_back = 9        # Travel time from Alamo Square back to Golden Gate Park (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Golden Gate Park at 9:00 AM (540 minutes)
ashley_start = 17 * 60 + 45    # Ashley will be at Alamo Square from 5:45 PM (1065 minutes)
ashley_end = 21 * 60 + 30      # Ashley leaves at 9:30 PM (1290 minutes)
min_meeting_duration = 75       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_alamo)  # Must arrive at Alamo Square after traveling
s.add(meeting_start >= ashley_start)                          # Meeting must start after Ashley is available
s.add(meeting_start + min_meeting_duration <= ashley_end)    # Meeting must finish before Ashley leaves

# Ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the time when the meeting ends

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")