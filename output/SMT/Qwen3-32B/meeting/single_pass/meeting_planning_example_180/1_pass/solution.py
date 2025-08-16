from z3 import *
import json

# Convert time to minutes since midnight
def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Convert minutes to HH:MM format
def to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

# Initialize solver
solver = Solver()

# Variables
start_j = Int('start_j')
end_j = Int('end_j')
start_r = Int('start_r')
end_r = Int('end_r')

# Constraints for James
# Arrive at Mission District at 9:00 AM + 18 min = 558 (9:18 AM)
solver.add(start_j >= 558)  # arrival at Mission District
solver.add(start_j >= to_minutes("12:45"))  # James's earliest start
solver.add(end_j - start_j >= 75)  # minimum 75 minutes meeting
solver.add(end_j <= to_minutes("14:00"))  # James's latest end

# Constraints for Robert
# Arrive at Castro after travel from Mission District (7 min)
solver.add(start_r >= end_j + 7)  # arrival at Castro
solver.add(start_r >= to_minutes("12:45"))  # Robert's earliest start
solver.add(end_r - start_r >= 30)  # minimum 30 minutes meeting
solver.add(end_r <= to_minutes("15:15"))  # Robert's latest end

# Check for solution
if solver.check() == sat:
    model = solver.model()
    sj = model[start_j].as_long()
    ej = model[end_j].as_long()
    sr = model[start_r].as_long()
    er = model[end_r].as_long()
    
    # Build itinerary
    itinerary = [
        {"action": "meet", "person": "James", "start_time": to_time(sj), "end_time": to_time(ej)},
        {"action": "meet", "person": "Robert", "start_time": to_time(sr), "end_time": to_time(er)}
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))