from ortools.sat.python import cp_model

# Example data for friends (can be replaced with actual data)
friends = [
    {"name": "Alice", "location": "Park"},
    {"name": "Bob", "location": "Cafe"},
    {"name": "Charlie", "location": "Library"},
]

# Number of positions in the itinerary
num_positions = 5  # Example value; adjust based on your problem

# Create the model
model = cp_model.CpModel()

# Define decision variables
friend_vars = []
start_vars = []
end_vars = []

for i in range(num_positions):
    # Friend index variable: 0 to len(friends) - 1, or 9 if unused
    friend_var = model.NewIntVar(0, len(friends) - 1, f'friend_{i}')
    friend_vars.append(friend_var)

    # Start and end time variables (in minutes, e.g., 600 = 10:00 AM)
    start_var = model.NewIntVar(600, 1080, f'start_{i}')  # 10:00 AM to 6:00 PM
    end_var = model.NewIntVar(660, 1140, f'end_{i}')      # 11:00 AM to 7:00 PM

    start_vars.append(start_var)
    end_vars.append(end_var)

    # Add constraint: end time must be after start time
    model.Add(end_var > start_var)

# (Add more constraints here if needed, e.g., no overlapping meetings, etc.)

# Solve the model
solver = cp_model.CpSolver()
status = solver.Solve(model)

# Process and print the solution
itinerary = []
for i in range(num_positions):
    f_idx_val = solver.Value(friend_vars[i])
    if f_idx_val != 9:  # Assuming 9 means no meeting at this position
        start = solver.Value(start_vars[i])
        end = solver.Value(end_vars[i])
        friend = friends[f_idx_val]

        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"

        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": to_time(start),
            "end_time": to_time(end)
        })

# Output the itinerary
if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    for item in itinerary:
        print(f"Meet {item['person']} at {item['location']} from {item['start_time']} to {item['end_time']}")
else:
    print("No solution found.")