import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Days are 1 to 10
    days = range(1, 11)
    
    # Boolean variables for each day and city
    in_istanbul = [Bool(f"I_{d}") for d in days]
    in_london = [Bool(f"L_{d}") for d in days]
    in_santorini = [Bool(f"S_{d}") for d in days]
    
    # Constraint: Total days in each city
    solver.add(Sum([If(in_istanbul[i], 1, 0) for i in range(10)]) == 3)
    solver.add(Sum([If(in_london[i], 1, 0) for i in range(10)]) == 3)
    solver.add(Sum([If(in_santorini[i], 1, 0) for i in range(10)]) == 6)
    
    # Constraint: Each day must be in at least one city and at most two cities
    for i in range(10):
        solver.add(Or(in_istanbul[i], in_london[i], in_santorini[i]))
        solver.add(Not(And(in_istanbul[i], in_london[i], in_santorini[i])))
    
    # Constraint: No direct flight between Istanbul and Santorini
    for i in range(10):
        solver.add(Not(And(in_istanbul[i], in_santorini[i])))
    
    # Constraint: Must be in Santorini on day 5 and day 10
    solver.add(in_santorini[4])  # Day 5
    solver.add(in_santorini[9])  # Day 10
    
    # Constraint: Travel days must be between connected cities
    for i in range(10):
        # If in two cities, must be connected
        two_cities = And(
            Or(And(in_istanbul[i], in_london[i]), 
               And(in_london[i], in_santorini[i])),
            Not(in_santorini[i]) if in_istanbul[i] and in_london[i] else Not(in_istanbul[i])
        )
        solver.add(Implies(
            Or(And(in_istanbul[i], in_london[i]), 
               And(in_london[i], in_santorini[i]),
               And(in_istanbul[i], in_santorini[i])),
            two_cities
        ))
    
    # Constraint: Continuity of stays
    for i in range(9):  # Days 1-9 to check with next day
        # For Istanbul
        solver.add(Implies(
            And(in_istanbul[i], Not(in_istanbul[i+1])),
            Or(And(in_istanbul[i], in_london[i]))  # Leave via London
        ))
        solver.add(Implies(
            And(Not(in_istanbul[i]), in_istanbul[i+1]),
            Or(And(in_istanbul[i+1], in_london[i+1]))  # Arrive via London
        ))
        
        # For London
        solver.add(Implies(
            And(in_london[i], Not(in_london[i+1])),
            Or(And(in_london[i], in_istanbul[i]), And(in_london[i], in_santorini[i]))
        ))
        solver.add(Implies(
            And(Not(in_london[i]), in_london[i+1]),
            Or(And(in_london[i+1], in_istanbul[i+1]), And(in_london[i+1], in_santorini[i+1]))
        ))
        
        # For Santorini
        solver.add(Implies(
            And(in_santorini[i], Not(in_santorini[i+1])),
            Or(And(in_santorini[i], in_london[i]))  # Leave via London
        ))
        solver.add(Implies(
            And(Not(in_santorini[i]), in_santorini[i+1]),
            Or(And(in_santorini[i+1], in_london[i+1]))  # Arrive via London
        ))
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        
        # Determine the presence in each city for each day
        itinerary = []
        for d in range(10):
            day = d + 1
            cities = []
            if is_true(model.eval(in_istanbul[d])):
                cities.append("Istanbul")
            if is_true(model.eval(in_london[d])):
                cities.append("London")
            if is_true(model.eval(in_santorini[d])):
                cities.append("Santorini")
            itinerary.append((day, cities))
        
        # Group consecutive days with the same city set
        segments = []
        current_segment = None
        
        for day, cities in itinerary:
            city_str = " and ".join(cities)
            if current_segment is None:
                current_segment = {
                    'start_day': day,
                    'end_day': day,
                    'place': city_str
                }
            else:
                if current_segment['place'] == city_str:
                    current_segment['end_day'] = day
                else:
                    segments.append(current_segment)
                    current_segment = {
                        'start_day': day,
                        'end_day': day,
                        'place': city_str
                    }
        if current_segment is not None:
            segments.append(current_segment)
        
        # Format the segments into the required output
        output_segments = []
        for seg in segments:
            if seg['start_day'] == seg['end_day']:
                day_range = f"Day {seg['start_day']}"
            else:
                day_range = f"Day {seg['start_day']}-{seg['end_day']}"
            output_segments.append({
                'day_range': day_range,
                'place': seg['place']
            })
        
        # Output as JSON
        result = {'itinerary': output_segments}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()