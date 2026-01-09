from constraint import Problem

# Define the problem
problem = Problem()

# Add variables for each city's duration
problem.addVariables([f"duration_{city}" for city in cities], [required_days[city]])