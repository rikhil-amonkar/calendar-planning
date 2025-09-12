import z3
import json

def mins_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

solver = z3.Solver()

# Define variables
K_start = z3.Int('K_start')
K_end = z3.Int('K_end')
T_start = z3.Int('T_start')
T_end = z3.Int('T_end')

# Constraints for Kenneth's meeting (Mission District)
solver.add(K_start >= 720)  # 12:00 PM
solver.add(K_end >= K_start + 45)  # Minimum 45 minutes
solver.add(K_end <= 945)  # 3:45 PM

# Constraints for Thomas's meeting (Pacific Heights)
solver.add(T_start >= K_end + 16)  # Travel from Mission to PH takes 16 minutes
solver.add(T_start >= 930)  # 3:30 PM
solver.add(T_end >= T_start + 75)  # Minimum 75 minutes
solver.add(T_end <= 1155)  # 7:15 PM

if solver.check() == z3.sat:
    model = solver.model()
    k_start_val = model.evaluate(K_start).as_long()
    k_end_val = model.evaluate(K_end).as_long()
    t_start_val = model.evaluate(T_start).as_long()
    t_end_val = model.evaluate(T_end).as_long()

    itinerary = [
        {
            "action": "meet",
            "location": "Mission District",
            "person": "Kenneth",
            "start_time": mins_to_time(k_start_val),
            "end_time": mins_to_time(k_end_val)
        },
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Thomas",
            "start_time": mins_to_time(t_start_val),
            "end_time": mins_to_time(t_end_val)
        }
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")