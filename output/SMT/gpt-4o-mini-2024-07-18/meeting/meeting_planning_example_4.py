from z3 import *

# Create a Z3 solver instance
s = Solver()

# Travel times
travel_time_to_marina = 10  # Travel time from Presidio to Marina District in minutes
travel_time_back = 10        # Travel time from Marina District back to Presidio in minutes

# Constants for timing
arrival_time = 9 * 60      # Arrival in Presidio at 9:00 AM in minutes (540)
jessica_start = 9 * 60 + 15  # Jessica is available at Marina District starting at 9:15 AM (555)
jessica_end = 17 * 60 + 45   # Jessica leaves at 5:45 PM (1070)
min_meeting_duration = 60    # Minimum meeting duration in minutes

# Variable for meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_marina)  # Must arrive at Marina after travel
s.add(meeting_start >= jessica_start)                         # Meeting must start after Jessica is available
s.add(meeting_start + min_meeting_duration <= jessica_end)   # Meeting must finish before Jessica leaves

# Add a constraint to ensure you have time to return back after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")