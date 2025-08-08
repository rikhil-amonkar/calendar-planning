from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Initialize Z3 solver
s = Solver()

# Define variables for start and end times of each meeting
S_j = Int('S_j')  # Joseph start time in minutes
E_j = Int('E_j')  # Joseph end time
S_k = Int('S_k')  # Karen start time
E_k = Int('E_k')  # Karen end time
S_b = Int('S_b')  # Kimberly start time
E_b = Int('E_b')  # Kimberly end time

# Convert time windows to minutes
joseph_start_min = 11 * 60 + 30  # 11:30
joseph_end_min = 12 * 60 + 45    # 12:45
karen_start_min = 14 * 60 + 30   # 14:30
karen_end_min = 19 * 60 + 45     # 19:45
kimberly_start_min = 15 * 60 + 45 # 15:45
kimberly_end_min = 19 * 60 + 15   # 19:15
laura_start_min = 19 * 60 + 45   # 19:45
laura_end_min = 21 * 60 + 30     # 21:30

# Travel times in minutes
travel_fw_to_as = 20  # Fisherman's Wharf to Alamo Square
travel_as_to_rh = 13  # Alamo Square to Russian Hill
travel_rh_to_nb = 5   # Russian Hill to North Beach
travel_nb_to_castro = 22  # North Beach to The Castro

# Start time at Fisherman's Wharf
start_fw = 9 * 60  # 9:00 AM

# Constraints for Joseph
s.add(S_j >= start_fw + travel_fw_to_as)  # Arrival time at Alamo Square
s.add(S_j >= joseph_start_min)             # Must start after Joseph's availability
s.add(E_j <= joseph_end_min)               # Must end before Joseph's window closes
s.add(E_j - S_j >= 15)                     # Minimum meeting duration

# Constraints for Karen
s.add(S_k >= E_j + travel_as_to_rh)        # Travel from Alamo Square to Russian Hill
s.add(S_k >= karen_start_min)              # Must start after Karen's availability
s.add(E_k <= karen_end_min)                # Must end before Karen's window closes
s.add(E_k - S_k >= 30)                     # Minimum meeting duration

# Constraints for Kimberly
s.add(S_b >= E_k + travel_rh_to_nb)        # Travel from Russian Hill to North Beach
s.add(S_b >= kimberly_start_min)           # Must start after Kimberly's availability
s.add(E_b <= kimberly_end_min)             # Must end before Kimberly's window closes
s.add(E_b - S_b >= 30)                     # Minimum meeting duration

# Constraint to reach Laura on time
s.add(E_b + travel_nb_to_castro <= laura_start_min)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    # Extract meeting times
    S_j_val = model[S_j].as_long()
    E_j_val = model[E_j].as_long()
    S_k_val = model[S_k].as_long()
    E_k_val = model[E_k].as_long()
    S_b_val = model[S_b].as_long()
    E_b_val = model[E_b].as_long()
    
    # Format itinerary
    itinerary = [
        {"action": "meet", "person": "Joseph", "start_time": min_to_time(S_j_val), "end_time": min_to_time(E_j_val)},
        {"action": "meet", "person": "Karen", "start_time": min_to_time(S_k_val), "end_time": min_to_time(E_k_val)},
        {"action": "meet", "person": "Kimberly", "start_time": min_to_time(S_b_val), "end_time": min_to_time(E_b_val)},
        {"action": "meet", "person": "Laura", "start_time": "19:45", "end_time": "21:30"}
    ]
    
    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found")