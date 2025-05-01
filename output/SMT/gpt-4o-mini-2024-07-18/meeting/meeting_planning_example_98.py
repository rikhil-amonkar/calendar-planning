from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_richmond = 12  # Travel time from Alamo Square to Richmond District (in minutes)
travel_time_back = 13          # Travel time from Richmond District back to Alamo Square (in minutes)

# Constants for timing
arrival_time = 9 * 60            # Arrival at Alamo Square at 9:00 AM (540 minutes)
timothy_start = 20 * 60 + 45     # Timothy will be at Richmond District from 8:45 PM (1245 minutes)
timothy_end = 21 * 60 + 30       # Timothy leaves at 9:30 PM (1290 minutes)
min_meeting_duration = 45         # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_richmond)  # Must arrive at Richmond District after traveling
s.add(meeting_start >= timothy_start)                            # Meeting must start after Timothy is available
s.add(meeting_start + min_meeting_duration <= timothy_end)      # Meeting must finish before Timothy leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")