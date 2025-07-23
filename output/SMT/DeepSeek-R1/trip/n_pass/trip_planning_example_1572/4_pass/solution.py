from z3 import *

def main():
    cities = ['Berlin', 'Milan', 'Seville', 'Paris', 'Lyon', 'Nice', 'Naples', 'Zurich', 'Stockholm', 'Riga']
    n = len(cities)
    num_days = 23
    
    # Create Z3 variables for start and end days of each city
    start_vars = [Int(f'start_{city}') for city in cities]
    end_vars = [Int(f'end_{city}') for city in cities]
    
    # Create assignment variables for each day (1 to 23)
    assign_vars = [Int(f'assign_{d}') for d in range(1, num_days + 1)]
    
    s = Solver()
    
    # Each city must have a duration of at least 2 days
    for i in range(n):
        s.add(start_vars[i] >= 1)
        s.add(end_vars[i] <= num_days)
        s.add(end_vars[i] - start_vars[i] + 1 >= 2)
    
    # Assignment must be between 0 and n-1 (city indices)
    for d in range(num_days):
        s.add(assign_vars[d] >= 0, assign_vars[d] < n)
    
    # Consistency between assignment_vars and start_vars/end_vars
    for i in range(n):
        for d in range(1, num_days + 1):
            day_index = d - 1
            # If day d is within [start_vars[i], end_vars[i]], then assign_vars[day_index] must be i
            in_interval = And(d >= start_vars[i], d <= end_vars[i])
            s.add(If(in_interval, assign_vars[day_index] == i, assign_vars[day_index] != i))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Extract start and end days for each city
        visits = []
        for i, city in enumerate(cities):
            s_val = model.eval(start_vars[i]).as_long()
            e_val = model.eval(end_vars[i]).as_long()
            visits.append((city, s_val, e_val))
        
        # Sort visits by start day
        visits.sort(key=lambda x: x[1])
        
        # Build itinerary
        itinerary = []
        for visit in visits:
            city, s_val, e_val = visit
            day_range = f"Day {s_val}-{e_val}"
            itinerary.append({'day_range': day_range, 'place': city})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()