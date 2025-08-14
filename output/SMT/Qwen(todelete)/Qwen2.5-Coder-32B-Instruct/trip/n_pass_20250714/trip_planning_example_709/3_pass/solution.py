from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
helsinki_start = Int('helsinki_start')
prague_start = Int('prague_start')
valencia_start = Int('valencia_start')
porto_start = Int('porto_start')
dubrovnik_start = Int('dubrovnik_start')
reykjavik_start = Int('reykjavik_start')

# Define the durations for each city
helsinki_duration = 4
prague_duration = 3
valencia_duration = 5
porto_duration = 3
dubrovnik_duration = 4
reykjavik_duration = 4

# Define the constraints for the duration of stay in each city
solver.add(helsinki_start + helsinki_duration <= 19)
solver.add(prague_start + prague_duration <= 19)
solver.add(valencia_start + valencia_duration <= 19)
solver.add(porto_start + porto_duration <= 19)
solver.add(dubrovnik_start + dubrovnik_duration <= 19)
solver.add(reykjavik_start + reykjavik_duration <= 19)

# Add the constraint that Porto must be visited between day 16 and day 18
solver.add(And(porto_start >= 16, porto_start + porto_duration - 1 <= 18))

# Add the constraints for direct flights
# Helsinki -> Prague
solver.add(Or(helsinki_start + helsinki_duration <= prague_start, prague_start + prague_duration <= helsinki_start))
solver.add(Or(helsinki_start + helsinki_duration == prague_start, prague_start + prague_duration == helsinki_start))
# Prague -> Valencia
solver.add(Or(prague_start + prague_duration <= valencia_start, valencia_start + valencia_duration <= prague_start))
solver.add(Or(prague_start + prague_duration == valencia_start, valencia_start + valencia_duration == prague_start))
# Valencia -> Porto
solver.add(Or(valencia_start + valencia_duration <= porto_start, porto_start + porto_duration <= valencia_start))
solver.add(Or(valencia_start + valencia_duration == porto_start, porto_start + porto_duration == valencia_start))
# Helsinki -> Reykjavik
solver.add(Or(helsinki_start + helsinki_duration <= reykjavik_start, reykjavik_start + reykjavik_duration <= helsinki_start))
solver.add(Or(helsinki_start + helsinki_duration == reykjavik_start, reykjavik_start + reykjavik_duration == helsinki_start))
# Dubrovnik -> Helsinki
solver.add(Or(dubrovnik_start + dubrovnik_duration <= helsinki_start, helsinki_start + helsinki_duration <= dubrovnik_start))
solver.add(Or(dubrovnik_start + dubrovnik_duration == helsinki_start, helsinki_start + helsinki_duration == dubrovnik_start))
# Reykjavik -> Prague
solver.add(Or(reykjavik_start + reykjavik_duration <= prague_start, prague_start + prague_duration <= reykjavik_start))
solver.add(Or(reykjavik_start + reykjavik_duration == prague_start, prague_start + prague_duration == reykjavik_start))

# Ensure all start days are positive
solver.add(helsinki_start >= 1)
solver.add(prague_start >= 1)
solver.add(valencia_start >= 1)
solver.add(porto_start >= 1)
solver.add(dubrovnik_start >= 1)
solver.add(reykjavik_start >= 1)

# Ensure the total duration is exactly 18 days
max_day = Int('max_day')
solver.add(max_day == 18)

# Ensure the last day of the trip is exactly day 18
solver.add(Or(
    helsinki_start + helsinki_duration - 1 == max_day,
    prague_start + prague_duration - 1 == max_day,
    valencia_start + valencia_duration - 1 == max_day,
    porto_start + porto_duration - 1 == max_day,
    dubrovnik_start + dubrovnik_duration - 1 == max_day,
    reykjavik_start + reykjavik_duration - 1 == max_day
))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    helsinki_start_val = model[helsinki_start].as_long()
    prague_start_val = model[prague_start].as_long()
    valencia_start_val = model[valencia_start].as_long()
    porto_start_val = model[porto_start].as_long()
    dubrovnik_start_val = model[dubrovnik_start].as_long()
    reykjavik_start_val = model[reykjavik_start].as_long()

    # Create the itinerary
    itinerary = []
    def add_to_itinerary(start, duration, place):
        end = start + duration - 1
        itinerary.append({"day_range": f"Day {start}-{end}", "place": place})
        if start != end:
            itinerary.append({"day_range": f"Day {end}", "place": place})

    add_to_itinerary(helsinki_start_val, helsinki_duration, "Helsinki")
    add_to_itinerary(prague_start_val, prague_duration, "Prague")
    add_to_itinerary(valencia_start_val, valencia_duration, "Valencia")
    add_to_itinerary(porto_start_val, porto_duration, "Porto")
    add_to_itinerary(dubrovnik_start_val, dubrovnik_duration, "Dubrovnik")
    add_to_itinerary(reykjavik_start_val, reykjavik_duration, "Reykjavik")

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    # Print the itinerary in JSON format
    print({"itinerary": itinerary})
else:
    print("No solution found")