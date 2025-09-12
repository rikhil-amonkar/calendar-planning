import z3
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define Z3 variables
s_start = z3.Int('s_start')
j_start = z3.Int('j_start')

# Constraints for Stephanie's meeting
# Must start after arriving at Embarcadero (9:00 AM) + 5 min travel to FD
stephanie_constraints = [
    s_start >= 9 * 60 + 5,  # 9:05 AM (545)
    s_start + 90 <= 11 * 60 + 30  # 11:30 AM (690)
]

# Constraints for John's meeting
# Must start after arriving from FD (s_start + 90 + 17) and after 10:15 AM
john_constraints = [
    j_start >= s_start + 90 + 17,  # Travel time FD->Alamo Square is 17 min
    j_start >= 10 * 60 + 15,       # 10:15 AM (615)
    j_start + 30 <= 20 * 60 + 45   # 8:45 PM (1245)
]

# Combine all constraints
constraints = stephanie_constraints + john_constraints

# Create and solve Z3 model
solver = z3.Solver()
solver.add(constraints)

if solver.check() == z3.sat:
    model = solver.model()
    s_start_val = model[s_start].as_long()
    j_start_val = model[j_start].as_long()

    # Calculate meeting times
    stephanie_start = s_start_val
    stephanie_end = s_start_val + 90
    john_start = j_start_val
    john_end = j_start_val + 30

    # Convert to time strings
    itinerary = [
        {
            "action": "meet",
            "location": "Financial District",
            "person": "Stephanie",
            "start_time": minutes_to_time(stephanie_start),
            "end_time": minutes_to_time(stephanie_end)
        },
        {
            "action": "meet",
            "location": "Alamo Square",
            "person": "John",
            "start_time": minutes_to_time(john_start),
            "end_time": minutes_to_time(john_end)
        }
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No valid meeting schedule found"}, indent=2))