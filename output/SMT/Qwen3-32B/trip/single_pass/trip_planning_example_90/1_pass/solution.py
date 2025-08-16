import z3
import json

# Initialize Z3 solver
solver = z3.Solver()

# Define variables for start and end days of each city
n_start = z3.Int('n_start')
n_end = z3.Int('n_end')
v_start = z3.Int('v_start')
v_end = z3.Int('v_end')
vi_start = z3.Int('vi_start')
vi_end = z3.Int('vi_end')

# Add constraints for Naples (must be 5 days from day 1 to 5)
solver.add(n_start == 1)
solver.add(n_end == 5)

# Flight from Naples to Vienna on day 5 (n_end)
solver.add(v_start == n_end)

# Vienna must be 7 days
solver.add(v_end == v_start + 6)

# Flight from Vienna to Vilnius on day v_end
solver.add(vi_start == v_end)

# Vilnius must be 7 days and end on day 17
solver.add(vi_end == vi_start + 6)
solver.add(vi_end == 17)

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    
    # Extract values from the model
    n_start_val = model[n_start].as_long()
    n_end_val = model[n_end].as_long()
    v_start_val = model[v_start].as_long()
    v_end_val = model[v_end].as_long()
    vi_start_val = model[vi_start].as_long()
    vi_end_val = model[vi_end].as_long()
    
    # Generate itinerary
    itinerary = []
    for day in range(1, 18):  # Days 1 through 17
        if day >= vi_start_val and day <= vi_end_val:
            city = "Vilnius"
        elif day >= v_start_val and day <= v_end_val:
            city = "Vienna"
        elif day >= n_start_val and day <= n_end_val:
            city = "Naples"
        else:
            city = "Unknown"
        itinerary.append({"day": day, "city": city})
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")