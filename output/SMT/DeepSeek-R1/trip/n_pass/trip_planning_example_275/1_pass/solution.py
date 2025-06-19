from z3 import Solver, Int, And, sat

# Initialize the solver
s = Solver()

# Define flight days: f1 (Vilnius to Split), f2 (Split to Madrid), f3 (Madrid to Santorini)
f1 = Int('f1')
f2 = Int('f2')
f3 = 13  # Fixed flight day to Santorini

# Constraints for flight days
s.add(And(f1 >= 1, f1 < f2, f2 < f3, f3 == 13))
# Days in Vilnius: from day 1 to f1 (inclusive) -> f1 days
s.add(f1 == 4)
# Days in Split: from f1 to f2 (inclusive) -> (f2 - f1 + 1) days
s.add(f2 - f1 + 1 == 5)
# Days in Madrid: from f2 to f3 (inclusive) -> (f3 - f2 + 1) days
s.add(13 - f2 + 1 == 6)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    f1_val = model[f1].as_long()
    f2_val = model[f2].as_long()
    f3_val = 13
    
    # Build the itinerary
    itinerary = [
        {"day_range": f"Day 1-{f1_val}", "place": "Vilnius"},
        {"day_range": f"Day {f1_val}", "place": "Vilnius"},
        {"day_range": f"Day {f1_val}", "place": "Split"},
        {"day_range": f"Day {f1_val}-{f2_val}", "place": "Split"},
        {"day_range": f"Day {f2_val}", "place": "Split"},
        {"day_range": f"Day {f2_val}", "place": "Madrid"},
        {"day_range": f"Day {f2_val}-{f3_val}", "place": "Madrid"},
        {"day_range": f"Day {f3_val}", "place": "Madrid"},
        {"day_range": f"Day {f3_val}", "place": "Santorini"},
        {"day_range": f"Day {f3_val}-14", "place": "Santorini"}
    ]
    
    # Output the result as a JSON-formatted dictionary
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No valid itinerary found.")