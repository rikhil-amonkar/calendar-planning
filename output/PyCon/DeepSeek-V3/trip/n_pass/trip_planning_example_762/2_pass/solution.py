city_order = range(len(cities))
problem.addVariables(city_order, range(len(cities)))  # Adds variables 0,1,2,3,4,5

day_city_vars = list(range(total_days))
problem.addVariables(day_city_vars, cities)  # Tries to add variable 0 again