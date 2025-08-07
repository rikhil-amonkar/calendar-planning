from z3 import *
import json

def main():
    # City mapping: 0=Istanbul, 1=London, 2=Santorini
    city_names = {0: 'Istanbul', 1: 'London', 2: 'Santorini'}
    
    # Create 11 variables: c0 to c10
    c = [Int(f'c_{i}') for i in range(11)]
    
    solver = Solver()
    
    # Each city variable must be 0, 1, or 2
    for var in c:
        solver.add(Or(var == 0, var == 1, var == 2))
    
    # Flight constraints between consecutive days
    for i in range(1, 11):
        prev = c[i-1]
        curr = c[i]
        solver.add(Or(
            prev == curr,
            And(prev == 0, curr == 1),
            And(prev == 1, curr == 0),
            And(prev == 1, curr == 2),
            And(prev == 2, curr == 1)
        ))
    
    # Count days for each city
    total_istanbul = 0
    total_london = 0
    total_santorini = 0
    
    for i in range(1, 11):
        start = c[i-1]
        end = c[i]
        total_istanbul += If(Or(start == 0, end == 0), 1, 0)
        total_london += If(Or(start == 1, end == 1), 1, 0)
        total_santorini += If(Or(start == 2, end == 2), 1, 0)
    
    solver.add(total_istanbul == 3)
    solver.add(total_london == 3)
    solver.add(total_santorini == 6)
    
    # Conference constraints
    # Day 5: either start (c4) or end (c5) is Santorini
    solver.add(Or(c[4] == 2, c[5] == 2))
    # Day 10: either start (c9) or end (c10) is Santorini
    solver.add(Or(c[9] == 2, c[10] == 2))
    
    # Check and get solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(1, 11):
            city_val = model.evaluate(c[day])
            city_index = city_val.as_long()
            place = city_names[city_index]
            itinerary.append({'day': day, 'place': place})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()