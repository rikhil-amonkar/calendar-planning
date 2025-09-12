from z3 import *
import json

# Define cities as an EnumSort
Cities, (Krakow, Paris, Seville) = EnumSort('Cities', ['Krakow', 'Paris', 'Seville'])

# Create variables for the order of cities
first_city = Const('first_city', Cities)
second_city = Const('second_city', Cities)
third_city = Const('third_city', Cities)

solver = Solver()

# All cities must be distinct
solver.add(Distinct(first_city, second_city, third_city))

# Allowed transitions between cities
trans1 = Or(
    And(first_city == Krakow, second_city == Paris),
    And(first_city == Paris, second_city == Krakow),
    And(first_city == Paris, second_city == Seville),
    And(first_city == Seville, second_city == Paris)
)
solver.add(trans1)

trans2 = Or(
    And(second_city == Krakow, third_city == Paris),
    And(second_city == Paris, third_city == Krakow),
    And(second_city == Paris, third_city == Seville),
    And(second_city == Seville, third_city == Paris)
)
solver.add(trans2)

# Define durations based on city
duration1 = If(first_city == Krakow, 5, If(first_city == Paris, 2, 6))
duration2 = If(second_city == Krakow, 5, If(second_city == Paris, 2, 6))
duration3 = If(third_city == Krakow, 5, If(third_city == Paris, 2, 6))

# Compute start and end days for each city
start1 = 1
end1 = start1 + duration1 - 1
start2 = end1
end2 = start2 + duration2 - 1
start3 = end2
end3 = start3 + duration3 - 1

# Total trip duration is 11 days
solver.add(end3 == 11)

# Workshop in Krakow must occur between day 1 and 5
solver.add(Implies(second_city == Krakow, end1 <= 5))
solver.add(Implies(third_city == Krakow, end2 <= 5))

if solver.check() == sat:
    model = solver.model()
    
    # Extract city names from the model
    fc = model[first_city].decl().name()
    sc = model[second_city].decl().name()
    tc = model[third_city].decl().name()
    
    # Evaluate the end days
    end1_val = model.eval(end1).as_long()
    end2_val = model.eval(end2).as_long()
    end3_val = model.eval(end3).as_long()
    
    # Construct the itinerary
    itinerary = []
    itinerary.append({"day_range": f"Day 1-{end1_val}", "place": fc})
    itinerary.append({"day_range": f"Day {end1_val}-{end2_val}", "place": sc})
    itinerary.append({"day_range": f"Day {end2_val}-{end3_val}", "place": tc})
    
    # Output the result as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))