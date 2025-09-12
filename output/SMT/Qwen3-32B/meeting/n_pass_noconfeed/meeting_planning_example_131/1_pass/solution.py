import z3
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

solver = z3.Solver()

# Define variables
arrival_presidio = z3.Int('arrival_presidio')
s_j = z3.Int('s_j')
e_j = z3.Int('e_j')
duration_j = z3.Int('duration_j')
s_k = z3.Int('s_k')
e_k = z3.Int('e_k')
duration_k = z3.Int('duration_k')

# Constraints for arrival at Presidio (Pacific Heights to Presidio takes 11 minutes)
solver.add(arrival_presidio >= 551)  # 9:00AM + 11 minutes = 9:11AM = 551 minutes since midnight

# Jason's meeting constraints (Presidio)
solver.add(s_j >= arrival_presidio)
solver.add(s_j >= 600)  # 10:00AM = 600 minutes since midnight
solver.add(e_j == s_j + duration_j)
solver.add(duration_j >= 90)  # Minimum 90 minutes
solver.add(e_j <= 975)  # 4:15PM = 975 minutes since midnight

# Kenneth's meeting constraints (Marina District)
solver.add(s_k >= e_j + 10)  # Presidio to Marina takes 10 minutes
solver.add(s_k >= 930)  # 3:30PM = 930 minutes since midnight
solver.add(e_k == s_k + duration_k)
solver.add(duration_k >= 45)  # Minimum 45 minutes
solver.add(e_k <= 1005)  # 4:45PM = 1005 minutes since midnight

if solver.check() == z3.sat:
    model = solver.model()
    
    # Extract meeting times
    s_j_val = model.eval(s_j).as_long()
    e_j_val = model.eval(e_j).as_long()
    s_k_val = model.eval(s_k).as_long()
    e_k_val = model.eval(e_k).as_long()
    
    # Convert to time strings
    j_start = minutes_to_time(s_j_val)
    j_end = minutes_to_time(e_j_val)
    k_start = minutes_to_time(s_k_val)
    k_end = minutes_to_time(e_k_val)
    
    # Create JSON output
    itinerary = [
        {
            "action": "meet", 
            "location": "Presidio", 
            "person": "Jason", 
            "start_time": j_start, 
            "end_time": j_end
        },
        {
            "action": "meet", 
            "location": "Marina District", 
            "person": "Kenneth", 
            "start_time": k_start, 
            "end_time": k_end
        }
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No valid meeting schedule found.")