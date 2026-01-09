# Define the cities first
cities = ["Paris", "London", "Rome", "Berlin", "Madrid", "Amsterdam"]
city_order = range(len(cities))

# Add variables for the trip order (each position represents a day)
problem.addVariables(city_order, range(len(cities)))  # Values: 0-5 representing city indices

# For day-specific variables, use a different name to avoid conflict
day_vars = list(range(total_days))
problem.addVariables(day_vars, cities)  # Values: actual city names