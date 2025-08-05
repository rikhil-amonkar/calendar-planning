from z3 import Solver, Int, And, sat

def main():
    cities = ["Berlin", "Barcelona", "Lyon", "Nice", "Stockholm", "Athens", "Vilnius"]
    num_cities = len(cities)
    
    # Create start and end variables for each city
    s = [Int(f's_{i}') for i in range(num_cities)]
    e = [Int(f'e_{i}') for i in range(num_cities)]
    
    solver = Solver()
    
    # First city starts at day 1
    solver.add(s[0] == 1)
    # Last city ends at day 20
    solver.add(e[num_cities-1] == 20)
    
    # Cities are contiguous: next starts after previous ends
    for i in range(num_cities - 1):
        solver.add(s[i+1] == e[i] + 1)
    
    # Duration constraints: 2-4 days per city
    for i in range(num_cities):
        duration = e[i] - s[i] + 1
        solver.add(And(duration >= 2, duration <= 4))
    
    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_cities):
            start_val = model.eval(s[i]).as_long()
            end_val = model.eval(e[i]).as_long()
            day_range = f"Day {start_val}-{end_val}"
            itinerary.append({'day_range': day_range, 'place': cities[i]})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()