from z3 import Solver, Int, sat, model

# Convert time to minutes since midnight
def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Convert minutes back to time string
def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define variables
start_m = Int('start_m')
end_m = Int('end_m')
start_k = Int('start_k')
end_k = Int('end_k')

solver = Solver()

# Mark's constraints (available from 13:00 to 17:45 = 780 to 1065)
solver.add(start_m >= 780)  # 13:00
solver.add(end_m >= start_m + 120)  # Minimum 120 minutes
solver.add(end_m <= 1065)  # 17:45

# Karen's constraints (available from 18:45 to 20:15 = 1125 to 1215)
solver.add(start_k >= 1125)  # 18:45
solver.add(start_k >= end_m + 11)  # Travel time from Embarcadero to Pacific Heights (11 min)
solver.add(end_k >= start_k + 90)  # Minimum 90 minutes
solver.add(end_k <= 1215)  # 20:15

# Solve
if solver.check() == sat:
    model = solver.model()
    # Extract values
    start_m_val = model[start_m].as_long()
    end_m_val = model[end_m].as_long()
    start_k_val = model[start_k].as_long()
    end_k_val = model[end_k].as_long()
    
    # Format the itinerary
    itinerary = [
        {
            "action": "meet", 
            "person": "Mark", 
            "start_time": to_time_str(start_m_val), 
            "end_time": to_time_str(end_m_val)
        },
        {
            "action": "meet", 
            "person": "Karen", 
            "start_time": to_time_str(start_k_val), 
            "end_time": to_time_str(end_k_val)
        }
    ]
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")