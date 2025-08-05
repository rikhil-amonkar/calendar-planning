from z3 import Solver, Int, And, sat

def main():
    cities = ["Berlin", "Barcelona", "Lyon", "Nice", "Stockholm", "Athens", "Vilnius"]
    num_cities = len(cities)
    
    # Create start and end time variables for each city
    s = [Int(f's_{i}') for i in range(num_cities)]
    e = [Int(f'e_{i}') for i in range(num_cities)]
    
    solver = Solver()
    
    # Constraint: first city starts at day 1
    solver.add(s[0] == 1)
    # Constraint: last city ends at day 20
    solver.add(e[num_cities-1] == 20)
    
    # Constraint: contiguous trip - next city starts right after the previous one ends
    for i in range(num_cities - 1):
        solver.add(e[i] + 1 == s[i+1])
    
    # Constraint: each city is visited for at least 2 and at most 4 days
    for i in range(num_cities):
        duration = e[i] - s[i] + 1
        solver.add(And(duration >= 2, duration <= 4))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_cities):
            start_val = model[s[i]].as_long()
            end_val = model[e[i]].as_long()
            day_range = f"Day {start_val}-{end_val}"
            itinerary.append({'day_range': day_range, 'place': cities[i]})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()