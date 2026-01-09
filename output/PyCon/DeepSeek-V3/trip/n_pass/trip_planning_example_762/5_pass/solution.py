from constraint import Problem

# Define the cities first
cities = ["Paris", "London", "Rome", "Berlin", "Madrid", "Amsterdam"]
total_days = len(cities)

# Initialize the constraint problem
problem = Problem()

# Add variables for the trip order - use meaningful names to avoid conflicts
# Option 1: Use city indices (0-5) as values
problem.addVariables(range(total_days), range(total_days))

# Option 2: Or use city names directly as values
# problem.addVariables(range(total_days), cities)

# If you need both representations, you can create separate variable sets with different names
position_vars = [f"pos_{i}" for i in range(total_days)]
day_vars = [f"day_{i}" for i in range(total_days)]

problem.addVariables(position_vars, range(total_days))  # Values: 0-5 representing city indices
problem.addVariables(day_vars, cities)  # Values: actual city names

# Example constraint: all positions must be different
problem.addConstraint(AllDifferentConstraint(), position_vars)
problem.addConstraint(AllDifferentConstraint(), day_vars)