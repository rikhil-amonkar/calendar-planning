from z3 import Solver, Int, And, sat

def main():
    cities = ["Berlin", "Barcelona", "Lyon", "Nice", "Stockholm", "Athens", "Vilnius"]
    num_cities = len(cities)
    
    # Create start and duration variables for each city
    s = [Int(f's_{i}') for i in range(num_cities)]
    d = [Int(f'd_{i}') for i in range(num_cities)]
    
    solver = Solver()
    
    # Constraint: first city starts at day 1
    solver.add(s[0] == 1)
    
    # Constraint: next city starts at the end of the previous city (start[i] + duration[i])
    for i in range(num_cities - 1):
        solver.add(s[i+1] == s[i] + d[i])
    
    # Constraint: last city ends at day 20 (start[last] + duration[last] - 1 = 20)
    solver.add(s[num_cities-1] + d[num_cities-1] == 21)  # equivalent to end on day 20
    
    # Constraint: each city duration between 2 and 4 days
    for i in range(num_cities):
        solver.add(And(d[i] >= 2, d[i] <= 4))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_cities):
            start_val = model.eval(s[i]).as_long()
            dur_val = model.eval(d[i]).as_long()
            end_val = start_val + dur_val - 1
            day_range = f"Day {start_val}-{end_val}"
            itinerary.append({'day_range': day_range, 'place': cities[i]})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()