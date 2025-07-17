import z3

# Initialize optimizer for optimal scheduling
opt = z3.Optimize()

# Define variables in minutes from midnight
emily_start = z3.Int('emily_start')
william_start = z3.Int('william_start')

# Calculate end times
emily_end = emily_start + 45  # 45-minute meeting
william_end = william_start + 30  # 30-minute meeting

# Availability constraints
# Emily available: 18:30 (1110 minutes) to 22:00 (1320 minutes)
opt.add(emily_start >= 1110)
opt.add(emily_end <= 1320)

# William available: 19:30 (1170 minutes) to 21:30 (1290 minutes)
opt.add(william_start >= 1170)
opt.add(william_end <= 1290)

# Buffer constraint: 15 minutes between meetings
opt.add(z3.Or(
    william_start >= emily_end + 15,  # Emily first
    emily_start >= william_end + 15   # William first
))

# Define latest end time for optimization
last_end = z3.Int('last_end')
opt.add(last_end == z3.Max(emily_end, william_end))
opt.minimize(last_end)  # Find schedule that finishes earliest

# Check for solution
if opt.check() == z3.sat:
    m = opt.model()
    
    # Convert minutes to HH:MM format
    def to_time(minutes):
        return f"{minutes // 60:02d}:{minutes % 60:02d}"
    
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
    meetings = sorted(
        [emily_meeting, william_meeting],
        key=lambda x: x['start_time']
    )
    
    result = {'itinerary': meetings}
    print(result)
else:
    print("No valid solution found")