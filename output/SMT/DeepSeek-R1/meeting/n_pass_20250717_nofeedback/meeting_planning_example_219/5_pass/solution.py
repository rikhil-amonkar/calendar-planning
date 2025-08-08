import z3

# Initialize optimizer
opt = z3.Optimize()

# Define variables in minutes from midnight
emily_start = z3.Int('emily_start')
william_start = z3.Int('william_start')

# Calculate end times
emily_end = emily_start + 45  # 45-minute meeting
william_end = william_start + 30  # 30-minute meeting

# Availability constraints with proper boundaries
# Emily available: 18:30 (1110 minutes) to 22:00 (1320 minutes)
opt.add(emily_start >= 1110)
opt.add(emily_end <= 1320)  # Must end by 22:00

# William available: 19:30 (1170 minutes) to 21:30 (1290 minutes)
opt.add(william_start >= 1170)
opt.add(william_end <= 1290)  # Must end by 21:30

# Buffer constraint: 15 minutes between meetings
opt.add(z3.Or(
    william_start >= emily_end + 15,  # Emily first
    emily_start >= william_end + 15   # William first
))

# Define the first meeting start time for optimization
first_start = z3.If(emily_start <= william_start, emily_start, william_start)
opt.maximize(first_start)  # Schedule meetings as late as possible

# Check for solution
if opt.check() == z3.sat:
    m = opt.model()
    
    # Convert minutes to HH:MM format
    def to_time(minutes):
        h = minutes // 60
        m_val = minutes % 60
        return f"{h:02d}:{m_val:02d}"
    
    # Extract meeting times
    emily_meeting = {
        'action': 'meet',
        'person': 'Emily',
        'start_time': to_time(m[emily_start].as_long()),
        'end_time': to_time(m[emily_start].as_long() + 45)
    }
    william_meeting = {
        'action': 'meet',
        'person': 'William',
        'start_time': to_time(m[william_start].as_long()),
        'end_time': to_time(m[william_start].as_long() + 30)
    }
    
    # Sort meetings chronologically
    meetings = [emily_meeting, william_meeting]
    meetings.sort(key=lambda x: x['start_time'])
    
    result = {'itinerary': meetings}
    print(result)
else:
    print("No valid solution found")