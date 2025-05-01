from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_financial_district = 26  # Travel time from Golden Gate Park to Financial District (in minutes)
travel_time_back = 23                     # Travel time from Financial District back to Golden Gate Park (in minutes)

# Constants for timing
arrival_time = 9 * 60                   # Arrival at Golden Gate Park at 9:00 AM (540 minutes)
kenneth_start = 20 * 60                  # Kenneth arrives at Financial District at 8:00 PM (1200 minutes)
kenneth_end = 22 * 60                    # Kenneth leaves at 10:00 PM (120 minutes)
min_meeting_duration = 105                # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_financial_district)  # Must arrive at Financial District after traveling
s.add(meeting_start >= kenneth_start)                                      # Meeting must start after Kenneth arrives
s.add(meeting_start + min_meeting_duration <= kenneth_end)                # Meeting must finish before Kenneth leaves

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