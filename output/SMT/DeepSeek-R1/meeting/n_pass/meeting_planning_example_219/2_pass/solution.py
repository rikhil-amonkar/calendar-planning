import z3

# Initialize solver
s = z3.Solver()

# Define variables for start times
emily_start = z3.Int('emily_start')
william_start = z3.Int('william_start')

# Calculate end times based on durations
emily_end = emily_start + 45  # 45-minute meeting
william_end = william_start + 30  # 30-minute meeting

# Availability constraints:
# Emily available between 18:30 and 22:00
s.add(emily_start >= 18*60 + 30)  # 18:30 in minutes
s.add(emily_end <= 22*60)         # 22:00 in minutes

# William available between 19:30 and 21:30
s.add(william_start >= 19*60 + 30)  # 19:30 in minutes
s.add(william_end <= 21*60 + 30)    # 21:30 in minutes

# Ensure meetings don't overlap and have 15-minute buffer
s.add(z3.Or(
    william_start >= emily_end + 15,  # Emily first, then William
    emily_start >= william_end + 15   # William first, then Emily
))

# Check for a valid solution
if s.check() == z3.sat:
    m = s.model()
    # Helper function to convert minutes to "HH:MM" format
    def to_time(minutes):
        h = minutes // 60
        m_val = minutes % 60
        return f"{h:02d}:{m_val:02d}"
    
    # Get start times from model
    emily_start_val = m[emily_start].as_long()
    william_start_val = m[william_start].as_long()
    
    # Create meeting entries with time strings
    emily_meeting = {
        'action': 'meet',
        'person': 'Emily',
        'start_time': to_time(emily_start_val),
        'end_time': to_time(emily_start_val + 45)
    }
    william_meeting = {
        'action': 'meet',
        'person': 'William',
        'start_time': to_time(william_start_val),
        'end_time': to_time(william_start_val + 30)
    }
    
    # Sort meetings chronologically
    meetings = [
        (emily_start_val, emily_meeting),
        (william_start_val, william_meeting)
    ]
    meetings.sort(key=lambda x: x[0])
    itinerary = [meeting[1] for meeting in meetings]
    
    result = {'itinerary': itinerary}
    print(result)
else:
    print("No valid solution found")