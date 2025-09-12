import z3  # Make sure Z3 is imported

# Initialize the Z3 solver
solver = z3.Solver()

# Example: Declare S[i] and arrival_time as Z3 integer variables
# (You need to adjust this based on your actual variable definitions)
S = [z3.Int(f"S_{i}") for i in range(5)]  # Example: 5 integer variables
arrival_time = z3.Int("arrival_time")

# Example friend data
current_friend = {
    "available_start": 9  # Example available start time
}

# Add the constraint
i = 0  # Example index
solver.add(S[i] >= z3.If(arrival_time >= current_friend['available_start'], arrival_time, current_friend['available_start']))

# Check for satisfiability
if solver.check() == z3.sat:
    print("Solution exists:", solver.model())
else:
    print("No solution found.")