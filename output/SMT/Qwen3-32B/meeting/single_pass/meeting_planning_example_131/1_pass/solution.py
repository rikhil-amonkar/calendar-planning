import z3
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define constants
start_pacific = 9 * 60  # 540 minutes (9:00 AM)

# Jason's constraints
jason_start_min = 10 * 60  # 600 minutes (10:00 AM)
jason_end_max = 16 * 60 + 15  # 975 minutes (4:15 PM)
jason_duration = 90

# Kenneth's constraints
kenneth_start_min = 15 * 60 + 30  # 930 minutes (3:30 PM)
kenneth_end_max = 16 * 60 + 45  # 1005 minutes (4:45 PM)
kenneth_duration = 45

# Travel times
travel_pacific_to_presidio = 11
travel_presidio_to_marina = 10

# Z3 variables
S_j = z3.Int('S_j')
S_k = z3.Int('S_k')

solver = z3.Solver()

# Constraints for Jason's meeting
solver.add(S_j >= jason_start_min)
solver.add(S_j + jason_duration <= jason_end_max)
# Additional constraint to allow Kenneth's meeting
solver.add(S_j <= 860)  # because S_j + 100 <= 960

# Constraints for Kenneth's meeting
solver.add(S_k >= S_j + jason_duration + travel_presidio_to_marina)
solver.add(S_k >= kenneth_start_min)
solver.add(S_k + kenneth_duration <= kenneth_end_max)

if solver.check() == z3.sat:
    model = solver.model()
    sj_val = model[S_j].as_long()
    sk_val = model[S_k].as_long()
    # Compute end times
    ej_val = sj_val + jason_duration
    ek_val = sk_val + kenneth_duration
    # Create the itinerary
    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": to_time_str(sj_val), "end_time": to_time_str(ej_val)},
        {"action": "meet", "person": "Kenneth", "start_time": to_time_str(sk_val), "end_time": to_time_str(ek_val)}
    ]
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")