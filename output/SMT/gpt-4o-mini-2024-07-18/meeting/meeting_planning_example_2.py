from z3 import *

# Create a Z3 solver instance
s = Solver()

# Constants for time and travel
arrival_time = 9 * 60  # Arrival at Haight-Ashbury at 9:00 AM in minutes
travel_time_to_sunset = 15  # Travel time from Haight-Ashbury to Sunset District
travel_time_back = 15        # Travel time from Sunset District back to Haight-Ashbury

# Jessica's availability
jessica_start = 15 * 60 + 15  # 3:15 PM in minutes
jessica_end = 20 * 60 + 15    # 8:15 PM in minutes
minimum_meeting_duration = 90  # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_sunset)  # Must arrive at Sunset District after travelling
s.add(meeting_start >= jessica_start)                        # Meeting must start after Jessica is available
s.add(meeting_start + minimum_meeting_duration <= jessica_end)  # Must finish meeting before Jessica leaves

# Add constraint to ensure there is time to return to Haight-Ashbury after the meeting
s.add(meeting_start + minimum_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + minimum_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")