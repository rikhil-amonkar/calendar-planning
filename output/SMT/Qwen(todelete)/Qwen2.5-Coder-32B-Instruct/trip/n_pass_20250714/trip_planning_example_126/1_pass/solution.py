from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
start_seville = Int('start_seville')
start_paris = Int('start_paris')
start_krakow = Int('start_krakow')

# Define the duration of stay in each city
duration_seville = 6
duration_paris = 2
duration_krakow = 5

# Constraints for the duration of stay in each city
solver.add(start_seville + duration_seville <= 12)  # Seville stays within 11 days
solver.add(start_paris + duration_paris <= 12)      # Paris stays within 11 days
solver.add(start_krakow + duration_krakow <= 12)    # Krakow stays within 11 days

# Constraint for the workshop in Krakow
solver.add(And(start_krakow >= 1, start_krakow + duration_krakow - 1 <= 5))

# Constraints for direct flights
# If you fly from Krakow to Paris, you must spend a day in both cities
solver.add(Or(
    And(start_paris == start_krakow + duration_krakow),
    And(start_krakow == start_paris + duration_paris)
))

# If you fly from Paris to Seville, you must spend a day in both cities
solver.add(Or(
    And(start_seville == start_paris + duration_paris),
    And(start_paris == start_seville + duration_seville)
))

# Ensure all days are within the 11-day limit
solver.add(start_seville >= 1)
solver.add(start_paris >= 1)
solver.add(start_krakow >= 1)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_seville_val = model[start_seville].as_long()
    start_paris_val = model[start_paris].as_long()
    start_krakow_val = model[start_krakow].as_long()
    
    # Create the itinerary
    itinerary = []
    
    # Add Seville days
    itinerary.append({"day_range": f"Day {start_seville_val}-{start_seville_val + duration_seville - 1}", "place": "Seville"})
    if start_paris_val == start_seville_val + duration_seville:
        itinerary.append({"day_range": f"Day {start_seville_val + duration_seville - 1}", "place": "Seville"})
        itinerary.append({"day_range": f"Day {start_seville_val + duration_seville - 1}", "place": "Paris"})
    
    # Add Paris days
    itinerary.append({"day_range": f"Day {start_paris_val}-{start_paris_val + duration_paris - 1}", "place": "Paris"})
    if start_krakow_val == start_paris_val + duration_paris:
        itinerary.append({"day_range": f"Day {start_paris_val + duration_paris - 1}", "place": "Paris"})
        itinerary.append({"day_range": f"Day {start_paris_val + duration_paris - 1}", "place": "Krakow"})
    
    # Add Krakow days
    itinerary.append({"day_range": f"Day {start_krakow_val}-{start_krakow_val + duration_krakow - 1}", "place": "Krakow"})
    if start_paris_val == start_krakow_val + duration_krakow:
        itinerary.append({"day_range": f"Day {start_krakow_val + duration_krakow - 1}", "place": "Krakow"})
        itinerary.append({"day_range": f"Day {start_krakow_val + duration_krakow - 1}", "place": "Paris"})
    
    # Sort the itinerary by day range
    itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split()[1]))
    
    # Print the itinerary in JSON format
    print({"itinerary": itinerary})
else:
    print("No solution found")