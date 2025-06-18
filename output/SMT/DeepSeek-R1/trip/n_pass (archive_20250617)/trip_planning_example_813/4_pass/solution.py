from z3 import *

def main():
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    days = list(range(1, 18))  # Days 1 to 17

    edges = [
        ('Frankfurt', 'Dublin'),
        ('Frankfurt', 'London'),
        ('London', 'Dublin'),
        ('Vilnius', 'Frankfurt'),
        ('Frankfurt', 'Stuttgart'),
        ('Dublin', 'Seville'),
        ('London', 'Santorini'),
        ('Stuttgart', 'London'),
        ('Santorini', 'Dublin')
    ]
    
    # Build adjacency set of unordered pairs
    adj_set = set()
    for u, v in edges:
        key = (min(u, v), max(u, v))
        adj_set.add(key)
    
    # Build list of non-adjacent city pairs
    non_edges = []
    n = len(cities)
    for i in range(n):
        for j in range(i+1, n):
            c1 = cities[i]
            c2 = cities[j]
            key = (min(c1, c2), max(c1, c2))
            if key not in adj_set:
                non_edges.append((c1, c2))
    
    # Create Z3 variables: In[(city, day)] for each city and day
    In = {}
    for c in cities:
        for d in days:
            In[(c, d)] = Bool(f"In_{c}_{d}")
    
    s = Solver()
    
    # Constraint 1: For each day, the traveler is in 1 or 2 cities
    for d in days:
        in_cities = [In[(c, d)] for c in cities]
        total = Sum([If(in_c, 1, 0) for in_c in in_cities])
        s.add(Or(total == 1, total == 2))
        
        # Constraint: Non-adjacent cities cannot both be true on the same day
        for c1, c2 in non_edges:
            s.add(Or(Not(In[(c1, d)]), Not(In[(c2, d)])))
    
    # Constraint 2: Consecutive days must share at least one city
    for d in range(1, 17):
        common_city = Or([And(In[(c, d)], In[(c, d+1)]) for c in cities])
        s.add(common_city)
    
    # Constraint 3: Total days per city
    total_days_constraints = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    for c in cities:
        total = Sum([If(In[(c, d)], 1, 0) for d in days])
        s.add(total == total_days_constraints[c])
    
    # Constraint 4: Specific time windows
    s.add(Or(In[('London', 9)], In[('London', 10)]))
    s.add(Or(In[('Stuttgart', 7)], In[('Stuttgart', 8)], In[('Stuttgart', 9)]))
    
    # Additional constraints: First and last day must be non-travel days
    s.add(Sum([If(In[(c, 1)], 1, 0) for c in cities]) == 1)
    s.add(Sum([If(In[(c, 17)], 1, 0) for c in cities]) == 1)
    
    # Block the previous solution
    previous_solution = {
        1: ['Vilnius'],
        2: ['Vilnius'],
        3: ['Vilnius', 'Frankfurt'],
        4: ['Frankfurt'],
        5: ['Frankfurt'],
        6: ['Frankfurt'],
        7: ['Frankfurt', 'Stuttgart'],
        8: ['Stuttgart'],
        9: ['London', 'Stuttgart'],
        10: ['Santorini', 'London'],
        11: ['Santorini', 'Dublin'],
        12: ['Dublin'],
        13: ['Seville', 'Dublin'],
        14: ['Seville'],
        15: ['Seville'],
        16: ['Seville'],
        17: ['Seville']
    }
    
    block = []
    for d in days:
        for c in cities:
            if c in previous_solution[d]:
                block.append(In[(c, d)])
            else:
                block.append(Not(In[(c, d)]))
    s.add(Not(And(block)))
    
    # Check and output the model
    if s.check() == sat:
        model = s.model()
        plan = {}
        for d in days:
            day_cities = []
            for c in cities:
                if is_true(model[In[(c, d)]]):
                    day_cities.append(c)
            plan[d] = day_cities
        
        # Print the plan
        for d in days:
            print(f"Day {d}: {plan[d]}")
        
        # Verify total days per city
        print("\nTotal days per city:")
        for c in cities:
            count = sum(1 for d in days if c in plan[d])
            print(f"{c}: {count} days")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()