from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Days are 1 to 12
    days = 12
    City = Datatype('City')
    City.declare('Dublin')
    City.declare('Riga')
    City.declare('Vilnius')
    City = City.create()
    
    # Variables for each day: which city are we in?
    day_city = [Const(f'day_{i}_city', City) for i in range(1, days + 1)]
    
    # Constraints for direct flights
    # Possible transitions:
    # Dublin <-> Riga
    # Riga <-> Vilnius
    # No direct flights between Dublin and Vilnius
    
    for i in range(1, days):
        prev_city = day_city[i-1]
        curr_city = day_city[i]
        # Transition constraints: only allowed direct flights
        s.add(Or(
            prev_city == curr_city,  # stay in the same city
            And(prev_city == City.Dublin, curr_city == City.Riga),
            And(prev_city == City.Riga, curr_city == City.Dublin),
            And(prev_city == City.Riga, curr_city == City.Vilnius),
            And(prev_city == City.Vilnius, curr_city == City.Riga)
        ))
    
    # Count days in each city
    dublin_days = Sum([If(day_city[i] == City.Dublin, 1, 0) for i in range(days)])
    riga_days = Sum([If(day_city[i] == City.Riga, 1, 0) for i in range(days)])
    vilnius_days = Sum([If(day_city[i] == City.Vilnius, 1, 0) for i in range(days)])
    
    s.add(dublin_days == 2)
    s.add(riga_days == 5)
    s.add(vilnius_days == 7)
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_val = m.evaluate(day_city[i])
            itinerary.append({"day": day_num, "city": str(city_val)})
        
        # Verify transitions
        # Also, ensure that the itinerary starts and ends correctly
        # But the constraints should handle this
        
        # Convert to the required JSON format
        result = {"itinerary": itinerary}
        return result
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))